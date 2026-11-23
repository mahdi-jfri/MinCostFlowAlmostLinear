module

public import MinCostFlow.LinkCut.Path.Rev

/-!
# The tag step of the path payload

`pathActBody` applies a tag `t₀`, kept in a block at `b` outside the record, to the payload of
the record at `a`, as `actVal`, `actSum` and `compTag` of `pathPayload` do. A tag holds a flow
change and a detector change. For an edge, both are added to the edge. For the summary, only a
present detector maximum moves, by the detector change. The tag of the record becomes the sum of
the two tags. Each sum is one `addBlock` call.

The work splits in three parts that run one after the other: the edge (`pathActBody`), the
summary (`pathActSumTail`) and the tag (`pathActTagTail`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.Gen.NodeLayout

/-- The sum of two numbers, written over the first, is the true sum when it fits. -/
theorem pathIntAt_add {m m' : ℕ → ℕ} {x d h K : ℕ} {zx zd : ℤ} (hx : PathIntAt m x h K zx)
    (hd : PathIntAt m d h K zd) (hv' : Valid m' x h K)
    (hval : intVal m' x h K = wrap h K (intVal m x h K + intVal m d h K))
    (hf : Fits h K (zd + zx)) : PathIntAt m' x h K (zd + zx) :=
  ⟨hv', by rw [hval, hx.2, hd.2, add_comm]; exact wrap_of_fits hf⟩

/-- The last part of `act [b, a, heap]`: add the tag at `b` to the tag of the record. -/
def pathActTagTail (addProc : ℕ) : Stmt :=
  .call 3 addProc [kAt 1 9 7, .reg 0, .reg 15, .reg 2] ;;
  .call 3 addProc [kAt 1 9 8, .bin .add (.reg 0) (.reg 15), .reg 15, .reg 2] ;;
  .ret (.const 0)

/-- The middle part of `act [b, a, heap]`: move a present detector maximum of the summary. -/
def pathActSumTail (addProc : ℕ) : Stmt :=
  .cond (.load (kAt 1 8 6))
    (.call 3 addProc [kAt 1 9 6, .bin .add (.reg 0) (.reg 15), .reg 15, .reg 2] ;;
     pathActTagTail addProc)
    (pathActTagTail addProc)

/-- `act [b, a, heap]` for the path payload. After the prologue, register `1` holds `a + 4`. -/
def pathActBody (addProc : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 1) (.const 9))) ;;
  .assign 1 (.bin .add (.reg 1) (.const 4)) ;;
  .cond (.load (.bin .add (.reg 1) (.const 6)))
    (.call 3 addProc [kAt 1 8 2, .reg 0, .reg 15, .reg 2] ;;
     .call 3 addProc [kAt 1 8 3, .bin .add (.reg 0) (.reg 15), .reg 15, .reg 2] ;;
     pathActSumTail addProc)
    (pathActSumTail addProc)

theorem pathActBody_noRand (addProc : ℕ) : (pathActBody addProc).NoRand := by
  simp [pathActBody, pathActSumTail, pathActTagTail, Stmt.NoRand]

/-- The run of `pathActTagTail`. -/
theorem pathActTagTail_runs {w h K addProc : ℕ} {p : Program} (ω : ℕ → Bool)
    (hadd : MeetsContract w p addProc (addBlockContract w h K)) {st : State} {b a heap : ℕ}
    {t₀ t : PathTag}
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = a) (hr2 : st.regs 2 = heap)
    (hr15 : st.regs 15 = K) (hah : a + (9 + 9 * K) ≤ heap) (hbh : b + 2 * K ≤ heap)
    (hbd : b + 2 * K ≤ a ∨ a + (9 + 9 * K) ≤ b)
    (hroom : heap + 2 * K < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (ht0 : PathTagAt st.mem b h K t₀) (ht : PathTagAt st.mem (a + (9 + 7 * K)) h K t)
    (hf : PathTagFits h K (t₀.compose t)) :
    ∃ o st' c, Runs w p ω (pathActTagTail addProc) st o st' c ∧
      (ZeroFrom st'.mem heap ∧
        (∀ y < heap, ¬ (a + (9 + 7 * K) ≤ y ∧ y < a + (9 + 9 * K)) → st'.mem y = st.mem y) ∧
        PathTagAt st'.mem (a + (9 + 7 * K)) h K (t₀.compose t)) ∧
      0 + c ≤ 2 * (80 * K + 80) + 30 := by
  unfold pathActTagTail
  refine runs_seq_addBlock (x := a + (9 + 7 * K)) (d := b) (heap := heap) hadd (by eval_expr)
    (by omega) (by omega) (by omega) (by omega) (by omega) ht.1.1 ht0.1.1 hz hroom ?_
  intro m₁ hz₁ hf₁ hv₁ hval₁ v₁ pos₁
  have hd0 : PathIntAt m₁ (b + K) h K t₀.detector :=
    pathIntAt_move ht0.2 fun i hi => hf₁ _ (by omega) (by omega)
  have hdt : PathIntAt st.mem (a + (9 + 8 * K)) h K t.detector := by
    have := ht.2; rwa [show a + (9 + 7 * K) + K = a + (9 + 8 * K) by omega] at this
  have hd1 : PathIntAt m₁ (a + (9 + 8 * K)) h K t.detector :=
    pathIntAt_move hdt fun i hi => hf₁ _ (by omega) (by omega)
  refine runs_seq_addBlock (x := a + (9 + 8 * K)) (d := b + K) (heap := heap) hadd
    (by eval_expr) (by omega) (by omega) (by omega) (by omega) (by omega) hd1.1 hd0.1 hz₁
    hroom ?_
  intro m₂ hz₂ hf₂ hv₂ hval₂ v₂ pos₂
  dsimp only at hf₂ hval₂
  refine runs_ret_le (by eval_expr) ?_ (by simp only [Expr.size_reg, Expr.size_const,
    Expr.size_bin, argsSize_cons, argsSize_nil, kAt, kOff]; omega)
  refine ⟨hz₂, fun y hy hn => (hf₂ y hy (by omega)).trans (hf₁ y hy (by omega)), ?_, ?_⟩
  · have := pathIntAt_add ht.1 ht0.1 hv₁ hval₁ hf.1
    exact pathIntAt_move this fun i hi => hf₂ _ (by omega) (by omega)
  · rw [show a + (9 + 7 * K) + K = a + (9 + 8 * K) by omega]
    exact pathIntAt_add hd1 hd0 hv₂ hval₂ hf.2

/-- The run of `pathActSumTail`. -/
theorem pathActSumTail_runs {w h K addProc : ℕ} {p : Program} (ω : ℕ → Bool)
    (hadd : MeetsContract w p addProc (addBlockContract w h K)) {st : State} {b a heap : ℕ}
    {t₀ t : PathTag} {s : PathSummary}
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = a) (hr2 : st.regs 2 = heap)
    (hr15 : st.regs 15 = K) (hah : a + (9 + 9 * K) ≤ heap) (hbh : b + 2 * K ≤ heap)
    (hbd : b + 2 * K ≤ a ∨ a + (9 + 9 * K) ≤ b)
    (hroom : heap + 2 * K < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (ht0 : PathTagAt st.mem b h K t₀) (hs : PathSummaryAt st.mem (a + (8 + 4 * K)) h K s)
    (ht : PathTagAt st.mem (a + (9 + 7 * K)) h K t)
    (hfs : PathSummaryFits h K (s.shift t₀)) (hft : PathTagFits h K (t₀.compose t)) :
    ∃ o st' c, Runs w p ω (pathActSumTail addProc) st o st' c ∧
      (ZeroFrom st'.mem heap ∧
        (∀ y < heap, ¬ (a + (8 + 4 * K) ≤ y ∧ y < a + (9 + 9 * K)) → st'.mem y = st.mem y) ∧
        PathSummaryAt st'.mem (a + (8 + 4 * K)) h K (s.shift t₀) ∧
        PathTagAt st'.mem (a + (9 + 7 * K)) h K (t₀.compose t)) ∧
      0 + c ≤ 3 * (80 * K + 80) + 80 := by
  unfold pathActSumTail
  obtain ⟨hg, hl, hd⟩ := hs
  refine runs_cond_le (v := st.mem (a + (8 + 6 * K))) (by eval_expr) ?_ ?_
  · intro hne
    cases hsd : s.detector with
    | none =>
      simp only [hsd] at hd
      rw [show a + (8 + 4 * K) + 2 * K = a + (8 + 6 * K) by omega] at hd
      exact absurd hd hne
    | some z =>
      simp only [hsd] at hd
      obtain ⟨hd1, hdz⟩ := hd
      rw [show a + (8 + 4 * K) + 2 * K + 1 = a + (9 + 6 * K) by omega] at hdz
      have hfz : Fits h K (t₀.detector + z) := by
        have := hfs.2.2
        simp only [PathSummary.shift, hsd, Option.map_some] at this
        rwa [add_comm] at this
      refine runs_seq_addBlock (x := a + (9 + 6 * K)) (d := b + K) (heap := heap) hadd
        (by eval_expr) (by omega) (by omega) (by omega) (by omega) (by omega) hdz.1 ht0.2.1 hz
        hroom ?_
      intro m₁ hz₁ hf₁ hv₁ hval₁ v₁ pos₁
      have hdz₁ := pathIntAt_add hdz ht0.2 hv₁ hval₁ hfz
      obtain ⟨o, st', c, hr, ⟨hz', hf', ht'⟩, hc⟩ :=
        pathActTagTail_runs (st := ⟨m₁, Function.update st.regs 3 v₁, pos₁⟩) ω hadd (by simp [hr0])
          (by simp [hr1]) (by simp [hr2]) (by simp [hr15]) hah hbh hbd
          hroom hz₁ (pathTagAt_move ht0 fun i hi => hf₁ _ (by omega) (by omega))
          (pathTagAt_move ht fun i hi => hf₁ _ (by omega) (by omega)) hft
      dsimp only at hf' hz' ht'
      refine ⟨o, st', c, hr, ⟨hz', fun y hy hn => (hf' y hy (by omega)).trans
        (hf₁ y hy (by omega)), ?_, ht'⟩, by
          simp only [Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load,
            argsSize_cons, argsSize_nil, kAt, kOff] at hc ⊢; omega⟩
      have hkeep : ∀ y < heap, ¬ (a + (9 + 6 * K) ≤ y ∧ y < a + (9 + 9 * K)) →
          st'.mem y = st.mem y :=
        fun y hy hn => (hf' y hy (by omega)).trans (hf₁ y hy (by omega))
      refine ⟨pathIntAt_move hg fun i hi => hkeep _ (by omega) (by omega),
        pathIntAt_move hl fun i hi => hkeep _ (by omega) (by omega), ?_⟩
      show match (s.shift t₀).detector with
        | none => st'.mem (a + (8 + 4 * K) + 2 * K) = 0
        | some z => st'.mem (a + (8 + 4 * K) + 2 * K) = 1 ∧
            PathIntAt st'.mem (a + (8 + 4 * K) + 2 * K + 1) h K z
      simp only [PathSummary.shift, hsd, Option.map_some]
      refine ⟨by rw [hkeep _ (by omega) (by omega)]; exact hd1, ?_⟩
      rw [show a + (8 + 4 * K) + 2 * K + 1 = a + (9 + 6 * K) by omega, add_comm z]
      exact pathIntAt_move hdz₁ fun i hi => hf' _ (by omega) (by omega)
  · intro h0
    cases hsd : s.detector with
    | some z =>
      simp only [hsd] at hd
      rw [show a + (8 + 4 * K) + 2 * K = a + (8 + 6 * K) by omega] at hd
      exact absurd (hd.1.symm.trans h0) (by decide)
    | none =>
      simp only [hsd] at hd
      obtain ⟨o, st', c, hr, ⟨hz', hf', ht'⟩, hc⟩ :=
        pathActTagTail_runs ω hadd hr0 hr1 hr2 hr15 hah hbh hbd hroom hz ht0 ht hft
      refine ⟨o, st', c, hr, ⟨hz', fun y hy hn => hf' y hy (by omega), ?_, ht'⟩, by
          simp only [Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load, kAt,
            kOff] at hc ⊢
          omega⟩
      refine ⟨pathIntAt_move hg fun i hi => hf' _ (by omega) (by omega),
        pathIntAt_move hl fun i hi => hf' _ (by omega) (by omega), ?_⟩
      show match (s.shift t₀).detector with
        | none => st'.mem (a + (8 + 4 * K) + 2 * K) = 0
        | some z => st'.mem (a + (8 + 4 * K) + 2 * K) = 1 ∧
            PathIntAt st'.mem (a + (8 + 4 * K) + 2 * K + 1) h K z
      simp only [PathSummary.shift, hsd, Option.map_none]
      rw [hf' _ (by omega) (by omega)]; exact hd

/-- `pathActBody` meets the tag contract of the path payload. -/
theorem pathAct_meetsContract {w h K f addProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (pathActBody addProc))
    (hadd : MeetsContract w p addProc (addBlockContract w h K)) :
    MeetsContract w p f
      (actContract pathPayload (pathLayout h K) (pathOk h K) w (pathCost K) (pathSpace K)) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨b, a₀, heap, rfl, hah, hbh, hbd, t₀, v, s, t, ht0, hv₀, hs, ht, hokv, hoks,
    hokt⟩, hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + (8 * K + 8) < 2 ^ w at hroom
  change b + 2 * K ≤ heap at hbh
  change b + 2 * K ≤ a₀ ∨ a₀ + (pathLayout h K).nodeStride ≤ b at hbd
  rw [pathLayout_stride] at hah hbd
  rw [pathLayout_offSum] at hs
  rw [pathLayout_offTag] at ht
  change PathTagAt mem b h K t₀ at ht0
  change PathValAt mem (a₀ + 6) h K v at hv₀
  change PathSummaryAt mem (a₀ + (12 + 4 * K)) h K s at hs
  change PathTagAt mem (a₀ + (13 + 7 * K)) h K t at ht
  change PathSummaryFits h K (s.shift t₀) at hoks
  change PathTagFits h K (t₀.compose t) at hokt
  have hK : mem (a₀ + 9) = K := hv₀.2.2.2.1
  have hv : PathEdgeAt mem (a₀ + 4 + 6) h K v := by
    have := hv₀.2.2.2.2; rwa [show a₀ + 6 + 4 = a₀ + 4 + 6 by omega] at this
  rw [show a₀ + (12 + 4 * K) = a₀ + 4 + (8 + 4 * K) by omega] at hs
  rw [show a₀ + (13 + 7 * K) = a₀ + 4 + (9 + 7 * K) by omega] at ht
  have haw := hwords a₀ (by simp)
  apply runs_start_le
  unfold pathActBody
  refine runs_seq_pathPrologue_le (by decide) (by simp [startState]) hK (by omega) ?_
  generalize ha : a₀ + 4 = a at hv hs ht ⊢
  have hah' : a + (9 + 9 * K) ≤ heap := by omega
  have hbd' : b + 2 * K ≤ a ∨ a + (9 + 9 * K) ≤ b := by omega
  -- The rest, from any memory that holds the new edge value.
  have finish : ∀ (st : State) (k : ℕ) (m : ℕ → ℕ), st.mem = m → st.regs 0 = b →
      st.regs 1 = a → st.regs 2 = heap → st.regs 15 = K → ZeroFrom m heap →
      (∀ y < heap, ¬ (a + 6 ≤ y ∧ y < a + (8 + 4 * K)) → m y = mem y) →
      PathEdgeAt m (a + 6) h K (pathPayload.actVal t₀ v) →
      k + (3 * (80 * K + 80) + 80) ≤ pathCost K →
      ∃ o st' c, Runs w p ω (pathActSumTail addProc) st o st' c ∧
        (actContract pathPayload (pathLayout h K) (pathOk h K) w (pathCost K)
          (pathSpace K)).post [b, a₀, heap] mem o.value st'.mem ∧ k + c ≤ pathCost K := by
    rintro st k m rfl h0 h1 h2 h15 hz' hfr hv' hk
    obtain ⟨o, st', c, hr, ⟨hz₂, hf₂, hs₂, ht₂⟩, hc⟩ :=
      pathActSumTail_runs ω hadd h0 h1 h2 h15 hah' hbh hbd' (by omega) hz'
        (pathTagAt_move ht0 fun i hi => hfr _ (by omega) (by omega))
        (pathSummaryAt_move hs fun i hi => hfr _ (by omega) (by omega))
        (pathTagAt_move ht fun i hi => hfr _ (by omega) (by omega)) hoks hokt
    have hkeep : ∀ y < heap, ¬ (a + 6 ≤ y ∧ y < a + (9 + 9 * K)) → st'.mem y = mem y :=
      fun y hy hy' => (hf₂ y hy (by omega)).trans (hfr y hy (by omega))
    refine ⟨o, st', c, hr, ⟨hz₂, fun y hy hy' => ?_, ?_⟩, by omega⟩
    · change ¬ (a₀ + 6 ≤ y ∧ y < a₀ + (pathLayout h K).nodeStride) at hy'
      rw [pathLayout_stride] at hy'
      exact hkeep y hy (by omega)
    · intro t₀' v₁ s₀ t₁ ht0' hv₁ hs₀ ht₁
      change PathTagAt mem b h K t₀' at ht0'
      change PathValAt mem (a₀ + 6) h K v₁ at hv₁
      change (pathLayout h K).SumAt mem (a₀ + (pathLayout h K).offSum) s₀ at hs₀
      change (pathLayout h K).TagAt mem (a₀ + (pathLayout h K).offTag) t₁ at ht₁
      rw [pathLayout_offSum] at hs₀
      rw [pathLayout_offTag] at ht₁
      change PathSummaryAt mem (a₀ + (12 + 4 * K)) h K s₀ at hs₀
      change PathTagAt mem (a₀ + (13 + 7 * K)) h K t₁ at ht₁
      rw [show a₀ + (12 + 4 * K) = a + (8 + 4 * K) by omega] at hs₀
      rw [show a₀ + (13 + 7 * K) = a + (9 + 7 * K) by omega] at ht₁
      obtain rfl := pathTagAt_unique ht0 ht0'
      obtain rfl := pathValAt_unique hv₀ hv₁
      obtain rfl := pathSummaryAt_unique hs hs₀
      obtain rfl := pathTagAt_unique ht ht₁
      show PathValAt st'.mem (a₀ + 6) h K (pathPayload.actVal t₀ v) ∧
        (pathLayout h K).SumAt st'.mem (a₀ + (pathLayout h K).offSum) (s.shift t₀) ∧
        (pathLayout h K).TagAt st'.mem (a₀ + (pathLayout h K).offTag) (t₀.compose t)
      rw [pathLayout_offSum, pathLayout_offTag]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.1
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.2.1
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.2.2.1
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.2.2.2.1
      · rw [show a₀ + 6 + 4 = a + 6 by omega]
        exact pathEdgeAt_move hv' fun i hi => hf₂ _ (by omega) (by omega)
      · rw [show a₀ + (12 + 4 * K) = a + (8 + 4 * K) by omega]; exact hs₂
      · rw [show a₀ + (13 + 7 * K) = a + (9 + 7 * K) by omega]; exact ht₂
  cases v with
  | none =>
    change mem (a + 6) = 0 at hv
    wram_step
    · exact absurd hv hcond
    · refine finish _ _ mem rfl (by simp [startState]) (by simp) (by simp [startState]) (by simp)
        hz (fun _ _ _ => rfl) hv ?_
      simp only [pathCost, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load]
      omega
  | some e =>
    obtain ⟨hh, hd, hg, hl, hfl, hdt⟩ := hv
    rw [show a + 6 + 2 = a + 8 by omega] at hg hl hfl hdt
    rw [show a + 8 + 2 * K = a + (8 + 2 * K) by omega] at hfl
    rw [show a + 8 + 3 * K = a + (8 + 3 * K) by omega] at hdt
    obtain ⟨-, -, hff, hfd⟩ := (hokv : PathEdgeFits h K (some (e.shift t₀)))
    wram_step
    swap
    · simp [startState, hh] at hcond
    refine runs_seq_addBlock (x := a + (8 + 2 * K)) (d := b) (heap := heap) hadd
      (by eval_expr) (by omega) (by omega) (by omega) (by omega) (by omega) hfl.1 ht0.1.1 hz
      (by omega) ?_
    intro m₁ hz₁ hf₁ hv₁ hval₁ v₁ pos₁
    have hfl₁ := pathIntAt_add hfl ht0.1 hv₁ hval₁ (by rw [add_comm]; exact hff)
    have hdt₁ : PathIntAt m₁ (a + (8 + 3 * K)) h K e.detector :=
      pathIntAt_move hdt fun i hi => hf₁ _ (by omega) (by omega)
    have hb₁ : PathIntAt m₁ (b + K) h K t₀.detector :=
      pathIntAt_move ht0.2 fun i hi => hf₁ _ (by omega) (by omega)
    refine runs_seq_addBlock (x := a + (8 + 3 * K)) (d := b + K) (heap := heap) hadd
      (by eval_expr) (by omega) (by omega) (by omega) (by omega) (by omega) hdt₁.1 hb₁.1 hz₁
      (by omega) ?_
    intro m₂ hz₂ hf₂ hv₂ hval₂ v₂ pos₂
    dsimp only at hf₂ hval₂
    have hdt₂ := pathIntAt_add hdt₁ hb₁ hv₂ hval₂ (by rw [add_comm]; exact hfd)
    have hkeep : ∀ y < heap, ¬ (a + (8 + 2 * K) ≤ y ∧ y < a + (8 + 2 * K) + K) →
        ¬ (a + (8 + 3 * K) ≤ y ∧ y < a + (8 + 3 * K) + K) → m₂ y = mem y :=
      fun y hy h1 h2 => (hf₂ y hy h2).trans (hf₁ y hy h1)
    refine finish _ _ m₂ rfl (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp) hz₂ (fun y hy hn => hkeep y hy (by omega) (by omega)) ?_ ?_
    · refine ⟨by rw [hkeep (a + 6) (by omega) (by omega) (by omega)]; exact hh,
        by rw [hkeep (a + 6 + 1) (by omega) (by omega) (by omega)]; exact hd, ?_, ?_, ?_, ?_⟩
      · rw [show a + 6 + 2 = a + 8 by omega]
        exact pathIntAt_move hg fun i hi => by apply hkeep <;> omega
      · rw [show a + 6 + 2 = a + 8 by omega]
        exact pathIntAt_move hl fun i hi => by apply hkeep <;> omega
      · rw [show a + 6 + 2 + 2 * K = a + (8 + 2 * K) by omega]
        show PathIntAt m₂ (a + (8 + 2 * K)) h K (e.flow + t₀.flow)
        rw [add_comm e.flow]
        exact pathIntAt_move hfl₁ fun i hi => hf₂ _ (by omega) (by omega)
      · rw [show a + 6 + 2 + 3 * K = a + (8 + 3 * K) by omega]
        show PathIntAt m₂ (a + (8 + 3 * K)) h K (e.detector + t₀.detector)
        rw [add_comm e.detector]
        exact hdt₂
    · simp only [pathCost, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load,
        argsSize_cons, argsSize_nil, kAt, kOff]
      omega

end MinCostFlow.LinkCut.Path
