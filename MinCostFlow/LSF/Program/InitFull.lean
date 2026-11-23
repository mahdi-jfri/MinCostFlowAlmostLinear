module

public import MinCostFlow.LSF.Program.InitProgram
public import MinCostFlow.LSF.Program.InitOneProgram

/-!
# Complete `Initialize` body for Lemma 5.4 (`n₀ ≥ 1`)

Combines the main path (`mainBody`, `2 ≤ n₀`) and the one-vertex path (`oneBody`, `n₀ = 1`) via a
top-level branch on `mem (g0Ptr + dgNOff) - 1`. `lsfInit_runs` satisfies the full initialization
clause of `DSRep.Implements` for `lsfDataStructure`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- Complete body of LSF `Initialize`: branches on `n₀ - 1 ≠ 0` to `mainBody` (`2 ≤ n₀`) or
`oneBody` (`n₀ = 1`). -/
def lsfInitBody (I : InitIdx) (bBlocks bWstr bStore8 h : ℕ) : Stmt :=
  .cond (.bin .sub (.load (.bin .add (.reg 0) (.const dgNOff))) (.const 1))
    (mainBody I h) (oneBody I bBlocks bWstr bStore8 h)

lemma lsfInitBody_noRand (I : InitIdx) (bBlocks bWstr bStore8 h : ℕ) :
    (lsfInitBody I bBlocks bWstr bStore8 h).NoRand :=
  ⟨mainBody_noRand I h, oneBody_noRand I bBlocks bWstr bStore8 h⟩

/-- Complete initialization correctness and cost bound (`n₀ ≥ 1`) for a fixed initial graph `G₀`,
also witnessing `s'.G₀ = G₀`. -/
theorem lsfInit_runs_for {w h : ℕ} {p : Program} {I : InitIdx} {bBlocks bWstr bStore8 : ℕ}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : ∀ G₀, MeetsContract w p I.prep (prepStageContract w G₀))
    (hwid : MeetsContract w p I.widths (widthsContract w))
    (htree : ∀ G₀ v ℓ₀ P_fp vList eList, MeetsContract w p I.tree
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList))
    (hord : ∀ G₀ T₀ vList eList, MeetsContract w p I.order
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (hlb : MeetsContract w p I.lb (wstrLBContract w))
    (hdec : MeetsContract w p I.decomp
      (decompPhaseContract w h (defaultC_ceil K_AN) bWT bLB bW bCopy bFlag bRoots
        decompPhaseCost))
    (hf : MeetsContract w p I.forest (fPhaseContract w h bG bA bWF))
    (hblocks : MeetsContract w p bBlocks (initOneBlocksContract w))
    (hwstr : MeetsContract w p bWstr (initOneWstrContract w h))
    (hs8 : MeetsContract w p bStore8 (storeArgsContract w 8))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPreFor c_AN K_AN w h G₀ args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w) :
    ∃ o st' c, Runs w p ω (lsfInitBody I bBlocks bWstr bStore8 h)
        (startState args mem pos) o st' c ∧
      ∃ s' x', s'.G₀ = G₀ ∧ (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
        lsfInitPost K_AN h args mem s' st'.mem ∧
        (LSFRep h).Respects (fun _ => False) (heapArg args)
          (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + (LSFRep h).phi (heapArg args) x' st'.mem ≤ lsfInitCost Q_AN c_AN K_AN h args mem := by
  have hpre' := hpre
  obtain ⟨v₀, ℓ₀, g0Ptr, vCap0, eCap0, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b,
    hargs, -, hh, hhw, -, hVne, hdg0, hg0, hvc, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre'
  have hb_eq : heapArg args = b := by rw [hargs]; rfl
  have hw16 : 16 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hn_eq : mem (g0Ptr + dgNOff) = G₀.n := hdg0.2.2.2.2.2.1
  have hn1 : 1 ≤ G₀.n := Finset.card_pos.mpr hVne
  have hg0_lt : g0Ptr + dgNOff < 2 ^ w := by
    have hsz : 4 ≤ dynGraphSize vCap0 eCap0 := by dsimp [dynGraphSize]; omega
    have hb_lt : b < 2 ^ w := by rw [hb_eq] at hsp; omega
    dsimp [dgNOff]; omega
  have hGn_lt : G₀.n < 2 ^ w := by
    have hle := (dynGraph_card_le hdg0).1
    have hvc_lt : vCap < 2 ^ w := hwords vCap (by rw [hargs]; simp)
    omega
  have hr0 : (startState args mem pos).regs 0 = g0Ptr := by
    rw [hargs]; simp [startState]
  have heval : (Expr.bin .sub (.load (.bin .add (.reg 0) (.const dgNOff))) (.const 1)).eval w
      (startState args mem pos) = some (G₀.n - 1) := by
    have hmem : (startState args mem pos).mem = mem := rfl
    have h2 : dgNOff < 2 ^ w := by dsimp [dgNOff]; omega
    have h1 : 1 < 2 ^ w := by omega
    have hsub_lt : G₀.n - 1 < 2 ^ w := by omega
    simp [Expr.eval, BinOp.eval, hr0, hmem, h2, h1, hg0_lt, hn_eq, hsub_lt]
  have hesz : (Expr.bin .sub (.load (.bin .add (.reg 0) (.const dgNOff))) (.const 1)).size = 6 := by
    decide
  by_cases h1 : G₀.n = 1
  · have hn1_mem : mem (args.getD 0 0 + dgNOff) = 1 := by
      rw [hargs]; simp only [List.getD_cons_zero]; rw [hn_eq, h1]
    obtain ⟨o, st', c, hr, s', x', hsG0, hrep, hpost, hresp, hc⟩ :=
      lsfInit_one_runs_for hlog hprep hblocks hwstr hs8 hs20 hs24 pos ω hwords hpre hz hsp hn1_mem
    refine ⟨o, st', 6 + c + 1, ?_, s', x', hsG0, hrep, hpost, hresp, by omega⟩
    rw [lsfInitBody, runs_cond_iff]
    exact ⟨0, c, by rwa [h1] at heval, by simpa using hr, by rw [hesz]⟩
  · have hn2 : 2 ≤ mem (args.getD 0 0 + dgNOff) := by
      rw [hargs]; simp only [List.getD_cons_zero]; rw [hn_eq]; omega
    obtain ⟨o, st', c, hr, s', x', hsG0, hrep, hpost, hresp, hc⟩ :=
      lsfInit_main_runs_slack_for hlog hprep hwid htree hord hlb hdec hf hs20 hs24 pos ω hwords hpre
        hz hsp hn2
    refine ⟨o, st', 6 + c + 1, ?_, s', x', hsG0, hrep, hpost, hresp, by omega⟩
    rw [lsfInitBody, runs_cond_iff]
    exact ⟨G₀.n - 1, c, heval, by simp [show G₀.n - 1 ≠ 0 by omega, hr], by rw [hesz]⟩

/-- Complete initialization correctness and cost bound (`n₀ ≥ 1`) matching the `init` clause of
`DSRep.Implements` for `lsfDataStructure`. -/
theorem lsfInit_runs {w h : ℕ} {p : Program} {I : InitIdx} {bBlocks bWstr bStore8 : ℕ}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : ∀ G₀, MeetsContract w p I.prep (prepStageContract w G₀))
    (hwid : MeetsContract w p I.widths (widthsContract w))
    (htree : ∀ G₀ v ℓ₀ P_fp vList eList, MeetsContract w p I.tree
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList))
    (hord : ∀ G₀ T₀ vList eList, MeetsContract w p I.order
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (hlb : MeetsContract w p I.lb (wstrLBContract w))
    (hdec : MeetsContract w p I.decomp
      (decompPhaseContract w h (defaultC_ceil K_AN) bWT bLB bW bCopy bFlag bRoots
        decompPhaseCost))
    (hf : MeetsContract w p I.forest (fPhaseContract w h bG bA bWF))
    (hblocks : MeetsContract w p bBlocks (initOneBlocksContract w))
    (hwstr : MeetsContract w p bWstr (initOneWstrContract w h))
    (hs8 : MeetsContract w p bStore8 (storeArgsContract w 8))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPre c_AN K_AN w h args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w) :
    ∃ o st' c, Runs w p ω (lsfInitBody I bBlocks bWstr bStore8 h)
        (startState args mem pos) o st' c ∧
      ∃ s' x', (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
        lsfInitPost K_AN h args mem s' st'.mem ∧
        (LSFRep h).Respects (fun _ => False) (heapArg args)
          (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + (LSFRep h).phi (heapArg args) x' st'.mem ≤ lsfInitCost Q_AN c_AN K_AN h args mem := by
  obtain ⟨G₀, hpre'⟩ := hpre
  obtain ⟨o, st', c, hr, s', x', -, hrep, hpost, hresp, hc⟩ :=
    lsfInit_runs_for hlog hprep hwid htree hord hlb hdec hf hblocks hwstr hs8 hs20 hs24 pos ω
      hwords hpre' hz hsp
  exact ⟨o, st', c, hr, s', x', hrep, hpost, hresp, hc⟩

end

end MinCostFlow.LSF.Program
