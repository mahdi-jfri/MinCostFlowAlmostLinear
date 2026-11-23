module

public import MinCostFlow.Chain.Ordered.Budget
public import MinCostFlow.Chain.Algorithm2
public import MinCostFlow.Chain.Theorem5_1Helpers

/-!
# Algorithm 2 with orders

Algorithm 2 (`alg:rebuildScheduleForDS`, `jtree.tex` lines 745–778) as in `Chain/Algorithm2.lean`,
run on Algorithm 1 with orders (`Chain/Ordered/Algorithm1.lean`). The state `Alg2State` and the
configuration `Alg2Config` do not change. The procedures keep their names in the namespace
`MinCostFlow.Chain.Ordered`.

The validity of a configuration asks for the ordered specification of Lemma 5.17
(`Alg2Config.ValidOrdNoHidden`, `Alg2Config.ValidOrd`) on the inputs whose lengths lie in a range
set by `Ψ` (`ChainToolSupply`). The lengths of the input history must satisfy `|log ℓ_e| ≤ Ψ`
(`HistoryLengthsInRange`), as for a hidden stable instance (Definition 4.4, item 5, page 14). The runtime factors of Theorem 5.1 carry
`lemma511TimeFactor`, with `M₀^{2/d}` in place of `M₀^{1/d}` (`alg2RuntimeBoundSR`,
`alg2CollapsedFactor`). `theorem51RuntimeConstant` is the constant of the final time factor
`alg2TimeFactor` of Theorem 5.1 with orders.

A history of the IPM consists of edge insertions and deletions (paper Definition 4.6, page 15);
`HistoryEdgeOnly` states this. Level `0` of the chain is ordered only for such histories.

A rebuild of level `0` renames the live internal edges to `0, …, |E| - 1`, in the order of their
old names (`Ordered.updateLoop`, `MGraph.compact`). `algorithm2_updateWith` renames its maps between
external and internal names with it (`level0E2I`, `level0I2E`) and sets `nextFresh` to `|E|`
(`level0NF`). So the internal names stay bounded (`Ordered/NextFreshBound.lean`).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section Algorithm2Def

/-- Initialize Algorithm 2 on `(G₀, g₀, ℓ₀)`, with Algorithm 1 with orders. -/
noncomputable def algorithm2_init (cfg : Alg2Config)
    (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ) : Alg2State cfg :=
  { chain := (algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀ g₀).1
    branD := 0
    passes := fun _ => 0
    extG := G₀
    extToInt := id
    intToExt := id
    nextFresh := G₀.E.sup id + 1
    extℓ := ℓ₀
    extg := g₀
    flow := fun _ => 0
    detectAccum := fun _ => 0
    lctUpdateOps := G₀.m
    lctDetectOps := 0
    largeBatchEnc := 0 }

lemma shiftRemainingBudget_lt_of_step {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} {Ψ_g : ℝ} (ch : ChainState T P) (i : Fin (P.d + 1))
    (hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound P Ψ_g ch.rebuildCount i.val) :
    let ch' := (algorithm1_shift T L P ch i.val).1
    shiftRemainingBudget P Ψ_g ch' < shiftRemainingBudget P Ψ_g ch := by
  set ch' := (algorithm1_shift T L P ch i.val).1
  have hRebEq : ch'.rebuildCount = ch.rebuildCount := by
    dsimp only [ch', algorithm1_shift]
    split_ifs <;> rfl
  have hShEq : ch'.shiftCount =
      fun j => if j = i.val then ch.shiftCount i.val + 1 else ch.shiftCount j := by
    dsimp only [ch', algorithm1_shift]
    split_ifs with hi
    · rfl
    · have hieq : i.val = P.d := by have := i.isLt; omega
      funext j
      simp [hieq]
  have hle_floor : ch.shiftCount i.val + 1 ≤
      Nat.floor (gameShiftBound P Ψ_g ch.rebuildCount i.val) := by
    refine Nat.le_floor ?_
    exact_mod_cast hCap
  dsimp only
  unfold shiftRemainingBudget
  rw [hRebEq]
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [hShEq]
    dsimp only
    by_cases hji : j.val = i.val
    · rw [ite_eq_left_iff.mpr (fun h => absurd hji h), hji]
      omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hji)]
  · rw [hShEq]
    dsimp only
    rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    omega

/-- Inner shift loop of **Algorithm 2** (`jtree.tex` lines 757–772), parameterized by the
acceptance quality threshold `κ`. -/
noncomputable def algorithm2_loopWith (cfg : Alg2Config) (κ : ℝ) (extG : MGraph) (e2i : ℕ → ℕ)
    (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) :
    ChainState cfg.T cfg.P × ℕ × (Fin (cfg.P.d + 1) → ℕ) × ℕ × Option (ℕ → ℝ) :=
  let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  let fc := algorithm1_findCycle ch
  let Δ_ext := liftEdgeFn extG e2i fc.1
  let offTree := (walkEdges fc.2.1 \ ch.toTreeChain.chainTree.E).card
  let lctOps' := lctOps + 2 * (offTree + 1)
  if _hGood : extG.inner g' Δ_ext / extG.lnorm ℓ' Δ_ext ≤ -(κ * cfg.α) then
    (ch, branD, passes, lctOps', some Δ_ext)
  else
    match _hElig : findEligibleLevel cfg.P.d Ψ_g passes with
    | none => (ch, branD, passes, lctOps', none)
    | some i =>
      if hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P Ψ_g ch.rebuildCount i.val then
        let curB := if i.val < cfg.P.d then ch.bran i.val else branD
        let wrapped := (curB + 1) % cfg.P.k = 0
        let ch' := (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1
        let branD' := if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k
        let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
          if i < j then 0
          else if j = i then (if wrapped then passes i + 1 else passes i)
          else passes j
        algorithm2_loopWith cfg κ extG e2i g' ℓ' ch' branD' passes' lctOps'
      else
        (ch, branD, passes, lctOps', none)
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step ch i hCap

/-- Inner shift loop of **Algorithm 2** (`jtree.tex` lines 757–772) using `alg2Kappa` at `cfg.N₀`. -/
noncomputable def algorithm2_loop (cfg : Alg2Config) (extG : MGraph) (e2i : ℕ → ℕ)
    (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) :
    ChainState cfg.T cfg.P × ℕ × (Fin (cfg.P.d + 1) → ℕ) × ℕ × Option (ℕ → ℝ) :=
  algorithm2_loopWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    extG e2i g' ℓ' ch branD passes lctOps

/-- Whether an update rebuilt level `0`: then every level was rebuilt and the internal names of
the level-`0` graph were renamed (`Ordered.updateLoop`). -/
def level0Rebuilt (d : ℕ) (oldReb newReb : ℕ → ℕ) : Bool :=
  decide (firstRebuiltLevel d oldReb newReb = some 0)

/-- The map from external to internal names after an update. If level `0` was rebuilt from the
graph `G`, the internal name `e'` of `G` became `compactRank G.E e'`. -/
def level0E2I (ren : Bool) (G : MGraph) (e2i : ℕ → ℕ) : ℕ → ℕ :=
  if ren then fun e => compactRank G.E (e2i e) else e2i

/-- The map from internal to external names after an update. If level `0` was rebuilt from the
graph `G`, the new internal name `j` is the old name `compactUnrank G.E j`. -/
def level0I2E (ren : Bool) (G : MGraph) (i2e : ℕ → ℕ) : ℕ → ℕ :=
  if ren then fun j => i2e (compactUnrank G.E j) else i2e

/-- The next fresh internal name after an update: `|E(G)|` if level `0` was rebuilt from `G`. -/
def level0NF (ren : Bool) (G : MGraph) (nf : ℕ) : ℕ :=
  if ren then G.m else nf

/-- **Algorithm 2 `Update(U, g', ℓ', η)`**, parameterized by quality threshold `κ`. -/
noncomputable def algorithm2_updateWith (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    Alg2State cfg × Option (ℕ → ℝ) :=
  let (extG', e2i', i2e', nf', U_int) :=
    translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
  let ℓ_int := fun e' => ℓ' (i2e' e')
  let g_int := fun e' => g' (i2e' e')
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
  let G₀' := (st.chain.G 0).applyBatch U_int
  let e2i'' := level0E2I ren G₀' e2i'
  let i2e'' := level0I2E ren G₀' i2e'
  let nf'' := level0NF ren G₀' nf'
  let (branD1, passes1) :=
    match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar =>
      (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  let (chEnd, branDEnd, passesEnd, lctOpsEnd, optΔ) :=
    algorithm2_loopWith cfg κ extG' e2i'' g' ℓ' ch1 branD1 passes1 (st.lctUpdateOps + U_ext.length)
  let encOverflow := st.largeBatchEnc + largeBatchEncCap cfg.P U_int
  match optΔ with
  | none =>
    ({ st with
        chain := chEnd
        branD := branDEnd
        passes := passesEnd
        extG := extG'
        extToInt := e2i''
        intToExt := i2e''
        nextFresh := nf''
        extℓ := ℓ'
        extg := g'
        lctUpdateOps := lctOpsEnd
        largeBatchEnc := encOverflow
        updateCount := st.updateCount + 1 }, none)
  | some Δ =>
    let inc : ℕ → ℝ := fun e =>
      if e ∈ extG'.E then -(η / extG'.inner g' Δ) * Δ e else 0
    ({ chain := chEnd
       branD := branDEnd
       passes := passesEnd
       extG := extG'
       extToInt := e2i''
       intToExt := i2e''
       nextFresh := nf''
       extℓ := ℓ'
       extg := g'
       flow := fun e => st.flow e + inc e
       detectAccum := fun e => st.detectAccum e + |inc e|
       lctUpdateOps := lctOpsEnd
       lctDetectOps := st.lctDetectOps
       largeBatchEnc := encOverflow
       updateCount := st.updateCount + 1 }, some Δ)

/-- **Algorithm 2 `Update(U, g', ℓ', η)`** (`alg:rebuildScheduleForDS`, `jtree.tex` lines 747–778):
translates `U` via fresh internal IDs, invokes Algorithm 1's `Update`, renames the internal IDs
if level `0` was rebuilt (`level0E2I`, `level0I2E`, `level0NF`), synchronizes rebuild
resets on `(branD, passes)`, runs `algorithm2_loop`, and updates LCT flow and `Detect`
accumulators upon returning a cycle. -/
noncomputable def algorithm2_update (cfg : Alg2Config) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    Alg2State cfg × Option (ℕ → ℝ) :=
  let (extG', e2i', i2e', nf', U_int) :=
    translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
  let ℓ_int := fun e' => ℓ' (i2e' e')
  let g_int := fun e' => g' (i2e' e')
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
  let G₀' := (st.chain.G 0).applyBatch U_int
  let e2i'' := level0E2I ren G₀' e2i'
  let i2e'' := level0I2E ren G₀' i2e'
  let nf'' := level0NF ren G₀' nf'
  let (branD1, passes1) :=
    match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar =>
      (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  let (chEnd, branDEnd, passesEnd, lctOpsEnd, optΔ) :=
    algorithm2_loopWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
      extG' e2i'' g' ℓ' ch1 branD1 passes1 (st.lctUpdateOps + U_ext.length)
  let encOverflow := st.largeBatchEnc + largeBatchEncCap cfg.P U_int
  match optΔ with
  | none =>
    ({ st with
        chain := chEnd
        branD := branDEnd
        passes := passesEnd
        extG := extG'
        extToInt := e2i''
        intToExt := i2e''
        nextFresh := nf''
        extℓ := ℓ'
        extg := g'
        lctUpdateOps := lctOpsEnd
        largeBatchEnc := encOverflow
        updateCount := st.updateCount + 1 }, none)
  | some Δ =>
    let inc : ℕ → ℝ := fun e =>
      if e ∈ extG'.E then -(η / extG'.inner g' Δ) * Δ e else 0
    ({ chain := chEnd
       branD := branDEnd
       passes := passesEnd
       extG := extG'
       extToInt := e2i''
       intToExt := i2e''
       nextFresh := nf''
       extℓ := ℓ'
       extg := g'
       flow := fun e => st.flow e + inc e
       detectAccum := fun e => st.detectAccum e + |inc e|
       lctUpdateOps := lctOpsEnd
       lctDetectOps := st.lctDetectOps
       largeBatchEnc := encOverflow
       updateCount := st.updateCount + 1 }, some Δ)

/-- Package Algorithm 2 with quality threshold `κ` as a `MinRatioFailDataStructure`. -/
noncomputable def algorithm2_dsWith (cfg : Alg2Config) (κ : ℝ) : MinRatioFailDataStructure where
  State := Alg2State cfg
  init := fun G₀ g₀ ℓ₀ => algorithm2_init cfg G₀ g₀ ℓ₀
  update := fun st U g' ℓ' η => algorithm2_updateWith cfg κ st U g' ℓ' η
  query := fun st e => algorithm2_query cfg st e
  detect := fun st => algorithm2_detect cfg st

/-- Package Algorithm 2 as a `MinRatioFailDataStructure` using `alg2Kappa`. -/
noncomputable def algorithm2_ds (cfg : Alg2Config) : MinRatioFailDataStructure where
  State := Alg2State cfg
  init := fun G₀ g₀ ℓ₀ => algorithm2_init cfg G₀ g₀ ℓ₀
  update := fun st U g' ℓ' η => algorithm2_update cfg st U g' ℓ' η
  query := fun st e => algorithm2_query cfg st e
  detect := fun st => algorithm2_detect cfg st

/-- Package Algorithm 2 as a `MinRatioFailDataStructure` using `alg2KappaOwn` (evaluating level
`d` at `levelM cfg.TP cfg.P cfg.P.d + 1`). -/
noncomputable def algorithm2_dsOwn (cfg : Alg2Config) : MinRatioFailDataStructure :=
  algorithm2_dsWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)


end Algorithm2Def

section FailureWrappers

/-- Wraps `algorithm2_dsWith cfg κ` as a `MinCostFlow.IPM.MinRatioDataStructureWithFailure`. -/
noncomputable def algorithm2_dsWithFailureWith (cfg : Alg2Config) (κ : ℝ) :
    MinCostFlow.IPM.MinRatioDataStructureWithFailure where
  State := (algorithm2_dsWith cfg κ).State
  init := (algorithm2_dsWith cfg κ).init
  update := (algorithm2_dsWith cfg κ).update
  query := (algorithm2_dsWith cfg κ).query
  detect := (algorithm2_dsWith cfg κ).detect

/-- Wraps `algorithm2_ds cfg` as a `MinCostFlow.IPM.MinRatioDataStructureWithFailure`. -/
noncomputable def algorithm2_dsWithFailure (cfg : Alg2Config) :
    MinCostFlow.IPM.MinRatioDataStructureWithFailure :=
  algorithm2_dsWithFailureWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)

/-- Wraps `algorithm2_dsOwn cfg` as a `MinCostFlow.IPM.MinRatioDataStructureWithFailure`. -/
noncomputable def algorithm2_dsWithFailureOwn (cfg : Alg2Config) :
    MinCostFlow.IPM.MinRatioDataStructureWithFailure :=
  algorithm2_dsWithFailureWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)


/-- Total number of edges returned by `Detect` calls in steps `1 .. T` for `algorithm2_dsWith cfg κ`. -/
noncomputable def alg2DetectSizeWith (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  (Finset.Icc 1 T).sum fun s =>
    if isUpdate s = false then
      ((algorithm2_dsWith cfg κ).detect
        (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (s - 1))).1.card
    else 0

/-- Total number of edges returned by `Detect` calls in steps `1 .. T`. -/
noncomputable def alg2DetectSize (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  alg2DetectSizeWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate T

/-- Total number of edges returned by `Detect` calls in steps `1 .. T` for `algorithm2_dsOwn`. -/
noncomputable def alg2DetectSizeOwn (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  alg2DetectSizeWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate T

end FailureWrappers

section ConfigAndFactors

/-- Validity hypotheses of `Alg2Config` for Algorithm 2 with orders, with the hidden-stability-free
side conditions of the tool (used for unconditional preservation of invariants, `Query`,
`Detect`, and worst-case bounds). The tool need only meet its specification on the inputs whose
lengths lie in the range of `ChainToolSupply` for `Λ = max 0 Ψ` (`hT`), and its average stretch
bound only for edge bounds `M ≤ M₀²` (`hMWU`). -/
structure _root_.MinCostFlow.Chain.Alg2Config.ValidOrdNoHidden (cfg : Alg2Config) : Prop where
  hTP : cfg.TP.Valid
  hLP : cfg.LP.Valid
  hT : ChainToolSupply cfg.T cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ)
  hL : cfg.L.IsSpec cfg.LP
  hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → cfg.σ_mwu n₁ ≤ cfg.σ_mwu n₂
  hσ_mwu_nn : 0 ≤ cfg.σ_mwu cfg.N₀
  hMWU : cfg.T.ToolMWUOrdRestartNoHiddenLe cfg.σ_mwu (cfg.P.M₀ ^ 2)
  hEmb : cfg.T.ToolEmbedsSurvivingOrdRestartNoHidden
  hNoReins : cfg.T.ToolNoReinsertOrdRestartNoHidden
  hγM₀ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.M₀
  hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k
  hα : 0 < cfg.α

/-- Full parameter validity hypotheses for **Theorem 5.1** and **Lemma 6.5** for Algorithm 2 with
orders: the ordered specification of Lemma 5.17 on the inputs of
`ChainToolSupply`, and the side conditions with hidden stability. -/
structure _root_.MinCostFlow.Chain.Alg2Config.ValidOrd (cfg : Alg2Config) : Prop where
  hTP : cfg.TP.Valid
  hLP : cfg.LP.Valid
  hT : ChainToolSupply cfg.T cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ)
  hL : cfg.L.IsSpec cfg.LP
  hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → cfg.σ_mwu n₁ ≤ cfg.σ_mwu n₂
  hσ_mwu_nn : 0 ≤ cfg.σ_mwu cfg.N₀
  hMWU : cfg.T.ToolMWUOrdRestartNoHiddenLe cfg.σ_mwu (cfg.P.M₀ ^ 2)
  hEmb : cfg.T.ToolEmbedsSurvivingOrdRestart
  hNoReins : cfg.T.ToolNoReinsertOrdRestart
  hγM₀ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.M₀
  hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k
  hα : 0 < cfg.α

lemma _root_.MinCostFlow.Chain.Alg2Config.ValidOrd.toNoHidden {cfg : Alg2Config}
    (hV : cfg.ValidOrd) :
    cfg.ValidOrdNoHidden where
  hTP := hV.hTP
  hLP := hV.hLP
  hT := hV.hT
  hL := hV.hL
  hσ_mwu_mono := hV.hσ_mwu_mono
  hσ_mwu_nn := hV.hσ_mwu_nn
  hMWU := hV.hMWU
  hEmb := hV.hEmb.toNoHidden
  hNoReins := hV.hNoReins.toNoHidden
  hγM₀ := hV.hγM₀
  hγk := hV.hγk
  hα := hV.hα

/-- The lengths of the history up to stage `T` satisfy `|log ℓ_e| ≤ Ψ` on the edges of each
stage. Hidden stability asks this at every stage (Definition 4.4, item 5, page 14: all weights and
lengths are bounded by `exp (log^{O(1)} m)`), and Algorithm 2 sets its parameter `Ψ` from it
(`jtree.tex`, Algorithm 2, lines 290–291). -/
def HistoryLengthsInRange (D : DynamicInstance) (T : ℕ) (Ψ : ℝ) : Prop :=
  ∀ t ≤ T, ∀ e ∈ (D.G t).E, |Real.log (D.ℓ t e)| ≤ Ψ

/-- A positive length with `|log ℓ| ≤ Ψ` lies in `[e^{-max 0 Ψ}, e^{max 0 Ψ}]`. -/
lemma exp_bounds_of_abs_log_le {x Ψ : ℝ} (hx : 0 < x) (h : |Real.log x| ≤ Ψ) :
    Real.exp (-max 0 Ψ) ≤ x ∧ x ≤ Real.exp (max 0 Ψ) := by
  have hΨ : Ψ ≤ max 0 Ψ := le_max_right 0 Ψ
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  refine ⟨?_, ?_⟩
  · calc Real.exp (-max 0 Ψ) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = x := Real.exp_log hx
  · calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ ≤ Real.exp (max 0 Ψ) := Real.exp_le_exp.mpr (by linarith)

/-- A history with log-lengths in `[-Ψ, Ψ]` has, at each stage, positive lengths in
`[e^{-max 0 Ψ}, e^{max 0 Ψ}]`. -/
lemma HistoryLengthsInRange.lenInRange {D : DynamicInstance} {T : ℕ} {Ψ : ℝ}
    (h : HistoryLengthsInRange D T Ψ) {t : ℕ} (ht : t ≤ T)
    (hpos : ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) : LenInRange (max 0 Ψ) (D.G t) (D.ℓ t) :=
  fun e he => exp_bounds_of_abs_log_le (hpos e he) (h t ht e he)

/-- Item 5 of hidden stability at stage `t` puts the lengths at stage `t` in
`[e^{-max 0 Ψ}, e^{max 0 Ψ}]`. -/
lemma lenInRange_of_hiddenStableAt {D : DynamicInstance} {α Ψ : ℝ} {c w : ℕ → ℕ → ℝ} {t : ℕ}
    (h : D.HiddenStableAt α Ψ c w t) : LenInRange (max 0 Ψ) (D.G t) (D.ℓ t) :=
  fun e he => exp_bounds_of_abs_log_le (h.2.2.2.2 e he).2.2.1 (h.2.2.2.2 e he).2.2.2

/-- A hidden-stable history up to stage `T` has log-lengths in `[-Ψ, Ψ]` up to stage `T`. -/
lemma historyLengthsInRange_of_hiddenStable {D : DynamicInstance} {T : ℕ} {α Ψ : ℝ}
    {c w : ℕ → ℕ → ℝ} (h : ∀ t ≤ T, D.HiddenStableAt α Ψ c w t) :
    HistoryLengthsInRange D T Ψ :=
  fun t ht e he => ((h t ht).2.2.2.2 e he).2.2.2

/-- Every batch of the history up to stage `T` consists of edge insertions and deletions, as the
updates of the IPM do (paper Definition 4.6, page 15). -/
def HistoryEdgeOnly (D : DynamicInstance) (T : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ u ∈ D.U t, IsEdgeUpdate u

/-- Unconditional Tree-Chain runtime bound `eq:restatingTimeBoundSR` (`jtree.tex` page 30) for
Algorithm 2 with orders, with the factor `lemma511TimeFactor`. -/
noncomputable def alg2RuntimeBoundSR (cfg : Alg2Config) (st : Alg2State cfg) : ℝ :=
  lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀ *
    ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
      ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i) +
    st.largeBatchEnc

/-- Combined amortized overhead factor in the global-threshold-floor bound
(`eq:restatingTimeBoundSR` after eliminating `s_i` and `r_i`) for Algorithm 2 with orders: the
factor `Chain.alg2CollapsedFactor` with `lemma511TimeFactor` in place of its first factor. -/
noncomputable def alg2CollapsedFactor (cfg : Alg2Config) : ℝ :=
  let Cfac := lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀
  let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  let Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
  let Rfac := 16 * ((cfg.P.d : ℝ) + 1) ^ 2 * 2 ^ cfg.P.d * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ cfg.P.d *
      (cfg.P.k : ℝ) * (logFactor cfg.P cfg.N₀) ^ 2 + ((cfg.P.d : ℝ) + 1) ^ 2 + 1
  (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac * Rfac +
    (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1)

/-- The constant `C_rt` of the time factor `alg2TimeFactor C_rt (47 / 48)` of Theorem 5.1 for
Algorithm 2 with orders, in terms of the constants `C_γ`, `C_ψ`, `C_N` of its hypotheses. It is
the constant `62 + 21 C_γ + 4 C_ψ + C_N` of `Chain.theorem_5_1` plus `2`: the factor `M₀^{2/d}`
adds `1` to the coefficient of `log^{23/24} M₀ · log log M₀`, and the factor `3` is absorbed by
the other `1`. -/
noncomputable def theorem51RuntimeConstant (C_γ C_ψ C_N : ℝ) : ℝ :=
  64 + 21 * C_γ + 4 * C_ψ + C_N

end ConfigAndFactors

end MinCostFlow.Chain.Ordered
