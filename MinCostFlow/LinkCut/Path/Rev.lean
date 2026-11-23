module

public import MinCostFlow.LinkCut.Path.Layout
public import MinCostFlow.LinkCut.Path.Block
public import MinCostFlow.MinRatio.PathPayloadFits
public import WordRAM.Tactic
public import MinCostFlow.LinkCut.Gen.Call

/-!
# The reversal step of the path payload

`pathRevBody` reverses the payload of one node record, as `revVal`, `revSum` and `revTag` of
`pathPayload` do: for an edge it flips the direction word and negates the gradient and the flow;
it negates the gradient of the summary and the flow of the tag. Lengths and detector values do
not change. Each negation is a `negBlock` call, so the scratch is left zero.

The results are exact when they fit in `K` limbs (`pathOk`). Negation can leave the range
(`-(-2^(hK-1))` does not fit), so this is a real condition.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.Gen.NodeLayout

/-- The representable payload values: every number fits in `K` limbs. -/
def pathOk (h K : ℕ) : PayloadOk (Option PathEdgeValue) PathSummary PathTag :=
  ⟨PathEdgeFits h K, PathSummaryFits h K, PathTagFits h K⟩

/-- The cost bound of every payload step of the path payload. -/
def pathCost (K : ℕ) : ℕ := 2000 * K + 2000

/-- The scratch bound of every payload step of the path payload. -/
def pathSpace (K : ℕ) : ℕ := 8 * K + 8

theorem pathLayout_stride (h K : ℕ) : (pathLayout h K).nodeStride = 13 + 9 * K := by
  simp only [nodeStride, pathLayout]; omega

theorem pathLayout_offSum (h K : ℕ) : (pathLayout h K).offSum = 12 + 4 * K := by
  simp only [offSum, pathLayout]; omega

theorem pathLayout_offTag (h K : ℕ) : (pathLayout h K).offTag = 13 + 7 * K := by
  simp only [offTag, pathLayout]; omega

/-! The payload procedures get the address `a` of a record. They first load `K` from word `9`
of the record (word `3` of the value block) into register `15`, and then move register `0` to
`a + 4`. From then on the edge value starts at offset `6`, the summary at `8 + 4 K`, and the tag
at `9 + 7 K`, all relative to register `0`. Offsets that depend on `K` are computed from
register `15` (`kOff`). -/

/-- The offset `c + d K`, with `K` in register `15`. -/
abbrev kOff (c d : ℕ) : Expr := .bin .add (.const c) (.bin .mul (.const d) (.reg 15))

/-- The address `base + c + d K`, with the base in register `r`. -/
abbrev kAt (r c d : ℕ) : Expr := .bin .add (.reg r) (kOff c d)

/-- The address `base + c + d K`, with the base in register `0`. -/
abbrev kAddr (c d : ℕ) : Expr := kAt 0 c d

/-- The first two statements of a payload procedure on the record in register `r`, followed
by `s`. -/
theorem runs_seq_pathPrologue_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {r a K k T : ℕ} {Q : Outcome → State → Prop} (hr : r ≠ 15)
    (h0 : st.regs r = a) (hK : st.mem (a + 9) = K) (ha : a + 9 < 2 ^ w)
    (hrest : ∃ o st' c, Runs w p ω s
      { st with regs := Function.update (Function.update st.regs 15 K) r (a + 4) } o st' c ∧
      Q o st' ∧ (k + 11) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.assign 15 (.load (.bin .add (.reg r) (.const 9))))
      (.seq (.assign r (.bin .add (.reg r) (.const 4))) s)) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h0)
    (Expr.eval_const (by omega)) ha) hK) ?_
  refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq (by
    simp only [Function.update_apply, hr, if_false]; exact h0))
    (Expr.eval_const (by omega)) (by omega)) ?_
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest
  refine ⟨o, st', c, hr, hq, ?_⟩
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
  omega

/-- The end of `pathRevBody`: negate the summary gradient and the tag flow. -/
def pathRevTail (negProc : ℕ) : Stmt :=
  .call 2 negProc [kAddr 8 4, .reg 15, .reg 1] ;;
  .call 2 negProc [kAddr 9 7, .reg 15, .reg 1] ;;
  .ret (.const 0)

/-- `rev [a, heap]` for the path payload. -/
def pathRevBody (negProc : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .assign 0 (.bin .add (.reg 0) (.const 4)) ;;
  .cond (.load (.bin .add (.reg 0) (.const 6)))
    (.store (.bin .add (.reg 0) (.const 7))
        (.bin .sub (.const 1) (.load (.bin .add (.reg 0) (.const 7)))) ;;
     .call 2 negProc [.bin .add (.reg 0) (.const 8), .reg 15, .reg 1] ;;
     .call 2 negProc [kAddr 8 2, .reg 15, .reg 1] ;;
     pathRevTail negProc)
    (pathRevTail negProc)

theorem pathRevBody_noRand (negProc : ℕ) : (pathRevBody negProc).NoRand := by
  simp [pathRevBody, pathRevTail, Stmt.NoRand]

theorem neg_of_fits {h K : ℕ} {z : ℤ} (hf : Fits h K (-z)) : wrap h K (-z) = -z :=
  wrap_of_fits hf

/-- The run of `pathRevTail`. -/
theorem pathRevTail_runs {w h K negProc : ℕ} {p : Program} (ω : ℕ → Bool)
    (hneg : MeetsContract w p negProc (negBlockContract w h K)) {st : State} {a heap : ℕ}
    {s : PathSummary} {t : PathTag}
    (hr0 : st.regs 0 = a) (hr1 : st.regs 1 = heap) (hr15 : st.regs 15 = K)
    (hah : a + (9 + 9 * K) ≤ heap)
    (hroom : heap + 2 * K < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (hs : PathSummaryAt st.mem (a + (8 + 4 * K)) h K s)
    (ht : PathTagAt st.mem (a + (9 + 7 * K)) h K t)
    (hfs : Fits h K (-s.gradient)) (hft : Fits h K (-t.flow)) :
    ∃ o st' c, Runs w p ω (pathRevTail negProc) st o st' c ∧
      (ZeroFrom st'.mem heap ∧
        (∀ y < heap, ¬ (a + (8 + 4 * K) ≤ y ∧ y < a + (8 + 4 * K) + K) →
          ¬ (a + (9 + 7 * K) ≤ y ∧ y < a + (9 + 7 * K) + K) → st'.mem y = st.mem y) ∧
        PathSummaryAt st'.mem (a + (8 + 4 * K)) h K s.reverse ∧
        PathTagAt st'.mem (a + (9 + 7 * K)) h K t.reverse) ∧
      0 + c ≤ 2 * (80 * K + 80) + 40 := by
  unfold pathRevTail
  refine runs_seq_negBlock (x := a + (8 + 4 * K)) (heap := heap) hneg (by eval_expr)
    (by omega) (by omega) (by omega) hs.1.1 hz hroom ?_
  intro m₁ hz₁ hf₁ hv₁ hval₁ v₁ pos₁
  have ht₁ : PathTagAt m₁ (a + (9 + 7 * K)) h K t :=
    pathTagAt_move ht fun i hi => hf₁ _ (by omega) (by omega)
  refine runs_seq_negBlock (x := a + (9 + 7 * K)) (heap := heap) hneg (by eval_expr)
    (by omega) (by omega) (by omega) ht₁.1.1 hz₁ hroom ?_
  intro m₂ hz₂ hf₂ hv₂ hval₂ v₂ pos₂
  dsimp only at hf₂ hv₂ hval₂
  refine runs_ret_le (by eval_expr) ?_ (by simp only [Expr.size_reg, Expr.size_const,
    Expr.size_bin, argsSize_cons, argsSize_nil, kAddr, kOff]; omega)
  dsimp only
  refine ⟨hz₂, fun y hy h1 h2 => (hf₂ y hy h2).trans (hf₁ y hy h1), ?_, ?_⟩
  · obtain ⟨hg, hl, hd⟩ := hs
    refine ⟨⟨fun i hi => ?_, ?_⟩, pathIntAt_move hl fun i hi => ?_, ?_⟩
    · rw [hf₂ _ (by omega) (by omega)]; exact hv₁ i hi
    · rw [intVal_congr (fun i hi => hf₂ _ (by omega) (by omega)), hval₁, hg.2]
      exact neg_of_fits hfs
    · rw [hf₂ _ (by omega) (by omega), hf₁ _ (by omega) (by omega)]
    · have e2 : m₂ (a + (8 + 4 * K) + 2 * K) = st.mem (a + (8 + 4 * K) + 2 * K) := by
        rw [hf₂ _ (by omega) (by omega), hf₁ _ (by omega) (by omega)]
      show match s.detector with
        | none => m₂ (a + (8 + 4 * K) + 2 * K) = 0
        | some z => m₂ (a + (8 + 4 * K) + 2 * K) = 1 ∧
            PathIntAt m₂ (a + (8 + 4 * K) + 2 * K + 1) h K z
      cases hzd : s.detector with
      | none => simp only [hzd] at hd; rw [e2]; exact hd
      | some z =>
        simp only [hzd] at hd
        exact ⟨by rw [e2]; exact hd.1, pathIntAt_move hd.2 fun i hi => by
          rw [hf₂ _ (by omega) (by omega), hf₁ _ (by omega) (by omega)]⟩
  · obtain ⟨hfl, hdt⟩ := ht₁
    refine ⟨⟨hv₂, ?_⟩, pathIntAt_move hdt fun i hi => ?_⟩
    · rw [hval₂, hfl.2]; exact neg_of_fits hft
    · show m₂ (a + (9 + 7 * K) + K + i) = m₁ (a + (9 + 7 * K) + K + i)
      exact hf₂ _ (by omega) (by omega)

/-- `pathRevBody` meets the reversal contract of the path payload. -/
theorem pathRev_meetsContract {w h K b negProc : ℕ} {p : Program}
    (hb : p.procs[b]? = some (pathRevBody negProc))
    (hneg : MeetsContract w p negProc (negBlockContract w h K)) :
    MeetsContract w p b
      (revContract pathPayload (pathLayout h K) (pathOk h K) w (pathCost K) (pathSpace K)) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a₀, heap, rfl, hah, v, s, t, hv₀, hs, ht, hokv, hoks, hokt⟩, hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + (8 * K + 8) < 2 ^ w at hroom
  rw [pathLayout_stride] at hah
  rw [pathLayout_offSum] at hs
  rw [pathLayout_offTag] at ht
  change PathValAt mem (a₀ + 6) h K v at hv₀
  change PathSummaryAt mem (a₀ + (12 + 4 * K)) h K s at hs
  change PathTagAt mem (a₀ + (13 + 7 * K)) h K t at ht
  have hK : mem (a₀ + 9) = K := hv₀.2.2.2.1
  have hv : PathEdgeAt mem (a₀ + 4 + 6) h K v := by
    have := hv₀.2.2.2.2; rwa [show a₀ + 6 + 4 = a₀ + 4 + 6 by omega] at this
  rw [show a₀ + (12 + 4 * K) = a₀ + 4 + (8 + 4 * K) by omega] at hs
  rw [show a₀ + (13 + 7 * K) = a₀ + 4 + (9 + 7 * K) by omega] at ht
  have hfs : Fits h K (-s.gradient) := hoks.1
  have hft : Fits h K (-t.flow) := hokt.1
  have haw := hwords a₀ (by simp)
  have hhw := hwords heap (by simp)
  apply runs_start_le
  unfold pathRevBody
  refine runs_seq_pathPrologue_le (by decide) (by simp [startState]) hK (by omega) ?_
  generalize ha : a₀ + 4 = a at hv hs ht ⊢
  have hah' : a + (9 + 9 * K) ≤ heap := by omega
  -- The tail, from any memory that holds the reversed value and the old summary and tag.
  have finish : ∀ (st : State) (k : ℕ) (m : ℕ → ℕ), st.mem = m → st.regs 0 = a →
      st.regs 1 = heap → st.regs 15 = K → ZeroFrom m heap →
      (∀ y < heap, ¬ (a + 6 ≤ y ∧ y < a + (8 + 4 * K)) → m y = mem y) →
      PathEdgeAt m (a + 6) h K (pathPayload.revVal v) →
      PathSummaryAt m (a + (8 + 4 * K)) h K s →
      PathTagAt m (a + (9 + 7 * K)) h K t →
      k + (2 * (80 * K + 80) + 40) ≤ pathCost K →
      ∃ o st' c, Runs w p ω (pathRevTail negProc) st o st' c ∧
        (revContract pathPayload (pathLayout h K) (pathOk h K) w (pathCost K)
          (pathSpace K)).post [a₀, heap] mem o.value st'.mem ∧ k + c ≤ pathCost K := by
    rintro st k m rfl h0 h1 h15 hz' hfr hv' hs' ht' hk
    obtain ⟨o, st', c, hr, ⟨hz₂, hf₂, hs₂, ht₂⟩, hc⟩ :=
      pathRevTail_runs ω hneg h0 h1 h15 hah' (by omega) hz' hs' ht' hfs hft
    have hkeep : ∀ y < heap, ¬ (a + 6 ≤ y ∧ y < a + (9 + 9 * K)) → st'.mem y = mem y :=
      fun y hy hy' => (hf₂ y hy (by omega) (by omega)).trans (hfr y hy (by omega))
    refine ⟨o, st', c, hr, ⟨hz₂, fun y hy hy' => ?_, ?_⟩, by omega⟩
    · change ¬ (a₀ + 6 ≤ y ∧ y < a₀ + (pathLayout h K).nodeStride) at hy'
      rw [pathLayout_stride] at hy'
      exact hkeep y hy (by omega)
    · intro v₁ s₁ t₁ hv₁ hs₁ ht₁
      change PathValAt mem (a₀ + 6) h K v₁ at hv₁
      change (pathLayout h K).SumAt mem (a₀ + (pathLayout h K).offSum) s₁ at hs₁
      change (pathLayout h K).TagAt mem (a₀ + (pathLayout h K).offTag) t₁ at ht₁
      rw [pathLayout_offSum] at hs₁
      rw [pathLayout_offTag] at ht₁
      change PathSummaryAt mem (a₀ + (12 + 4 * K)) h K s₁ at hs₁
      change PathTagAt mem (a₀ + (13 + 7 * K)) h K t₁ at ht₁
      rw [show a₀ + (12 + 4 * K) = a + (8 + 4 * K) by omega] at hs₁
      rw [show a₀ + (13 + 7 * K) = a + (9 + 7 * K) by omega] at ht₁
      obtain rfl := pathValAt_unique hv₀ hv₁
      obtain rfl := pathSummaryAt_unique hs hs₁
      obtain rfl := pathTagAt_unique ht ht₁
      show PathValAt st'.mem (a₀ + 6) h K (pathPayload.revVal v) ∧
        (pathLayout h K).SumAt st'.mem (a₀ + (pathLayout h K).offSum) s.reverse ∧
        (pathLayout h K).TagAt st'.mem (a₀ + (pathLayout h K).offTag) t.reverse
      rw [pathLayout_offSum, pathLayout_offTag]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.1
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.2.1
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.2.2.1
      · rw [hkeep _ (by omega) (by omega)]; exact hv₀.2.2.2.1
      · rw [show a₀ + 6 + 4 = a + 6 by omega]
        exact pathEdgeAt_move hv' fun i hi => hf₂ _ (by omega) (by omega) (by omega)
      · rw [show a₀ + (12 + 4 * K) = a + (8 + 4 * K) by omega]; exact hs₂
      · rw [show a₀ + (13 + 7 * K) = a + (9 + 7 * K) by omega]; exact ht₂
  cases v with
  | none =>
    change mem (a + 6) = 0 at hv
    wram_step
    · exact absurd hv hcond
    · refine finish _ _ mem rfl (by simp) (by simp [startState]) (by simp) hz (fun _ _ _ => rfl)
        hv hs ht ?_
      simp only [pathCost, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load]
      omega
  | some e =>
    obtain ⟨hh, hd, hg, hl, hfl, hdt⟩ := hv
    rw [show a + 6 + 2 = a + 8 by omega] at hg hl hfl hdt
    rw [show a + 6 + 1 = a + 7 by omega] at hd
    rw [show a + 8 + 2 * K = a + (8 + 2 * K) by omega] at hfl
    obtain ⟨hfg, -, hff, -⟩ := (hokv : PathEdgeFits h K (some e.reverse))
    wram_step
    swap
    · simp [startState, hh] at hcond
    refine runs_seq_store_named_le (x := a + 7) (v := 1 - mem (a + 7)) (by eval_expr)
      (by eval_expr) ?_
    intro M hM
    have hMy : ∀ y, y ≠ a + 7 → M y = mem y := fun y hy => by
      rw [hM]; exact Function.update_of_ne hy _ _
    refine runs_seq_negBlock (x := a + 8) (heap := heap) hneg (by eval_expr)
      (by omega) (by omega) (by omega)
      (pathIntAt_move hg fun i hi => hMy _ (by omega)).1 (fun y hy => by
        show M y = 0
        rw [hMy y (by omega)]; exact hz y hy) (by omega) ?_
    intro m₁ hz₁ hf₁ hv₁ hval₁ v₁ pos₁
    dsimp only at hf₁ hval₁
    refine runs_seq_negBlock (x := a + (8 + 2 * K)) (heap := heap) hneg (by eval_expr)
      (by omega) (by omega) (by omega)
      (pathIntAt_move hfl fun i hi => by
        show m₁ _ = _
        rw [hf₁ _ (by omega) (by omega), hMy _ (by omega)]).1 hz₁ (by omega) ?_
    intro m₂ hz₂ hf₂ hv₂ hval₂ v₂ pos₂
    dsimp only at hf₂ hval₂
    have hkeep : ∀ y < heap, y ≠ a + 7 → ¬ (a + 8 ≤ y ∧ y < a + 8 + K) →
        ¬ (a + (8 + 2 * K) ≤ y ∧ y < a + (8 + 2 * K) + K) → m₂ y = mem y :=
      fun y hy h7 h1 h2 => by rw [hf₂ y hy h2, hf₁ y hy h1, hMy y h7]
    have hback : ∀ y < heap, ¬ (a + 6 ≤ y ∧ y < a + (8 + 4 * K)) → m₂ y = mem y :=
      fun y hy hn => hkeep y hy (by omega) (by omega) (by omega)
    refine finish _ _ m₂ rfl (by simp) (by simp [startState]) (by simp) hz₂ hback ?_
      (pathSummaryAt_move hs fun i hi => by apply hback <;> omega)
      (pathTagAt_move ht fun i hi => by apply hback <;> omega) ?_
    · refine ⟨by rw [hkeep (a + 6) (by omega) (by omega) (by omega) (by omega)]; exact hh, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hf₂ _ (by omega) (by omega), hf₁ _ (by omega) (by omega), hM,
          Function.update_self, hd]
        cases hfw : e.forward <;> simp [PathEdgeValue.reverse, hfw]
      · rw [show a + 6 + 2 = a + 8 by omega]
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [hf₂ _ (by omega) (by omega)]; exact hv₁ i hi
        · rw [intVal_congr (fun i hi => hf₂ _ (by omega) (by omega)), hval₁,
            intVal_congr (fun i hi => hMy _ (by omega)), hg.2]
          exact wrap_of_fits hfg
      · rw [show a + 6 + 2 = a + 8 by omega]
        exact pathIntAt_move hl fun i hi => by apply hkeep <;> omega
      · rw [show a + 6 + 2 + 2 * K = a + (8 + 2 * K) by omega]
        refine ⟨hv₂, ?_⟩
        rw [hval₂, intVal_congr (fun i hi => by
          rw [hf₁ _ (by omega) (by omega), hMy _ (by omega)]), hfl.2]
        exact wrap_of_fits hff
      · rw [show a + 6 + 2 = a + 8 by omega]
        exact pathIntAt_move hdt fun i hi => by apply hkeep <;> omega
    · simp only [pathCost, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load,
        argsSize_cons, argsSize_nil, kAddr, kOff]
      omega

end MinCostFlow.LinkCut.Path
