module

public import MinCostFlow.MinRatio.WireInitBase
public import MinCostFlow.MinRatio.WireParamLookup
public import MinCostFlow.MinRatio.WireParamScalars
public import MinCostFlow.MinRatio.WireParamLevels
public import MinCostFlow.MinRatio.InitDepthLink
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# Uniform deterministic Word-RAM module for solver parameter setup (`WireParamProg`)

Assembles one fixed deterministic (`Stmt.NoRand`) Word-RAM procedure block `wireParamModule` that
computes `[d, branch, psi, quality, epsExp, N₀]`, `lvlM 0 .. lvlM (d - 1)` and the sparse-core
depth `chosenL (M₀ ^ 2)` from `[m, V, L, P, heap]` and meets `initParamSetupContract`:
- On small inputs `(m, V)` present in the finite table `entries`, `lookupEntries` writes the exact
  values at `heap .. heap + 6 + d` using only constants `0, 1, 2` for key matching and returns
  `heap + 7 + d` in `O(1)` fixed steps.
- On all other inputs, `wireParamEntryBody` runs `computeScalarParamsStmt` (`O(log m + log V)`),
  `prepareSolverChainWithDepthWorkspace` (`d = chosenD (23 / 24) M₀` and `branch = ⌈M₀^{1/d}⌉₊`,
  polylogarithmic in `M₀`), `prepareSolverSparseCoreWithDepthWorkspace` (`L = chosenL (M₀ ^ 2)`,
  polylogarithmic in `M₀`), and `computeGammaAndLevelsStmt` (`den`, `cap`, two `boundsProc` calls,
  `γ = 3 ^ L * g ^ (L + 1)`, `lvlM i = (M₀ * γ ^ (i + 1) + branch ^ i - 1) / branch ^ i`, and
  the depth `L` at `heap + 6 + d`, `O(log M₀ + L + d + K_bounds * log M₀)`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine Final

/-! ## Module layout and entry body -/

/-- Fixed length of `initDepthProcedures b 4` (independent of `b`). -/
@[expose] def wireParamDepthLen : ℕ := (initDepthProcedures 0 4).length

theorem initDepthProcedures_length_eq (b : ℕ) :
    (initDepthProcedures b 4).length = wireParamDepthLen := by
  rfl

/-- Offset of `clogTwoModule` inside `wireParamModule`. -/
@[expose] def wireParamClogOff : ℕ := 1 + wireParamDepthLen

/-- Offset of `boundsProcs` inside `wireParamModule`. -/
@[expose] def wireParamBoundsOff : ℕ := wireParamClogOff + 1

/-- Entry body of the uniform deterministic parameter-setup procedure. -/
@[expose] def wireParamEntryBody (depthBase clogProc boundsProc threshold A decK decThr witnessDen : ℕ)
    (entries : List (ℕ × ℕ × List ℕ)) : Stmt :=
  lookupEntries entries ;;
  computeScalarParamsStmt depthBase clogProc threshold A ;;
  prepareSolverChainWithDepthWorkspace threshold depthBase (depthBase + 1) (depthBase + 6)
    (depthBase + 2) 4 (depthBase + 5) .nop ;;
  prepareSolverSparseCoreWithDepthWorkspace depthBase (depthBase + 1) (depthBase + 6)
    (depthBase + 2) 4 .nop ;;
  computeGammaAndLevelsStmt decK decThr witnessDen boundsProc

/-- Complete self-contained deterministic procedure block for parameter setup placed at `b`,
with entry at `b + 0`. -/
@[expose] def wireParamModule (b threshold A decK decThr witnessDen : ℕ)
    (boundsProcs : ℕ → List Stmt) (entries : List (ℕ × ℕ × List ℕ)) : List Stmt :=
  [wireParamEntryBody (b + 1) (b + wireParamClogOff) (b + wireParamBoundsOff)
      threshold A decK decThr witnessDen entries] ++
  initDepthProcedures (b + 1) 4 ++
  Scaling.Machine.clogTwoModule (b + wireParamClogOff) ++
  boundsProcs (b + wireParamBoundsOff)

set_option exponentiation.threshold 512 in
private theorem prepareSolverChainWithDepthWorkspace_noRand
    (threshold bits load log roundEntry h branch : ℕ) :
    (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch .nop).NoRand := by
  simp [prepareSolverChainWithDepthWorkspace, initConcreteBucketBaseEdgeBound,
    solverChainWithDepthWorkspace, saveInitDepthNumericFormat, restoreInitDepthNumericFormat,
    initRuntimeWorkspaceChainDimensions, computeInitDepthLogRuntime,
    prepareInitDepthLogWorkspace, stageInitDepthLogBlock, stageInitDepthLogAccuracy,
    stageInitDepthLogWorkspace, computeInitDepthLogBlock, loadInitDepthLogPair,
    loadInitDepthLogInput, selectInitChainFromLogBlock, initRoundDepthLog,
    selectInitChainDimensions, searchInitDepth, scanInitDepth, advanceInitDepthCandidate,
    stageInitDepthPowers, finishInitChainDepth, testInitChainDepth, checkInitDepthBounds,
    initMinRatioCertifiedDimensions, initMinRatioBranchCountFrom, Stmt.NoRand]

private theorem prepareSolverSparseCoreWithDepthWorkspace_noRand
    (bits load log roundEntry h : ℕ) :
    (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h .nop).NoRand := by
  simp [prepareSolverSparseCoreWithDepthWorkspace, stageInitSparsifierEdgeCap,
    solverSparseCoreWithDepthWorkspace, saveInitDepthNumericFormat, restoreInitDepthNumericFormat,
    initRuntimeWorkspaceSparseCoreDepth, computeInitDepthLogRuntime,
    prepareInitDepthLogWorkspace, stageInitDepthLogBlock, stageInitDepthLogAccuracy,
    stageInitDepthLogWorkspace, computeInitDepthLogBlock, loadInitDepthLogPair,
    loadInitDepthLogInput, selectInitSparseCoreFromLogBlock, initRoundDepthLog,
    selectInitSparseCoreDepth, searchInitDepth, scanInitDepth, advanceInitDepthCandidate,
    stageInitDepthPowers, checkInitDepthBounds, Stmt.NoRand]

theorem wireParamEntryBody_noRand (depthBase clogProc boundsProc threshold A decK decThr witnessDen : ℕ)
    (entries : List (ℕ × ℕ × List ℕ)) :
    (wireParamEntryBody depthBase clogProc boundsProc threshold A decK decThr witnessDen entries).NoRand := by
  simp [wireParamEntryBody, lookupEntries_noRand, computeScalarParamsStmt_noRand,
    prepareSolverChainWithDepthWorkspace_noRand, prepareSolverSparseCoreWithDepthWorkspace_noRand,
    computeGammaAndLevelsStmt_noRand, Stmt.NoRand]

theorem wireParamModule_noRand (b threshold A decK decThr witnessDen : ℕ)
    (boundsProcs : ℕ → List Stmt) (entries : List (ℕ × ℕ × List ℕ))
    (hboundsNR : ∀ s ∈ boundsProcs (b + wireParamBoundsOff), s.NoRand) :
    ∀ s ∈ wireParamModule b threshold A decK decThr witnessDen boundsProcs entries, s.NoRand := by
  intro s hs
  unfold wireParamModule at hs
  simp only [List.mem_append, List.mem_singleton] at hs
  rcases hs with ((rfl | hdepth) | hclog) | hb
  · exact wireParamEntryBody_noRand _ _ _ _ _ _ _ _ _
  · exact initDepthProcedures_noRand _ _ s hdepth
  · simp only [Scaling.Machine.clogTwoModule, List.mem_singleton] at hclog
    subst hclog
    exact Scaling.Machine.clogTwoBody_noRand _
  · exact hboundsNR s hb

/-! ## Explicit space and cost bounds -/

/-- Scratch space used by `prepareSolverChainWithDepthWorkspace` at `M₀`. -/
@[expose] def wireParamChainDepthSpace (M₀ : ℕ) : ℕ :=
  let E := (M₀ + 2).size
  let q := 38 * (2 ^ 48 * E) ^ 8 + E
  let P := 4 * (q + E + 10)
  let L := P + E + 4
  L + L + Num.logarithmSpace L P E

/-- Scratch space used by `prepareSolverSparseCoreWithDepthWorkspace` at `M₀`. -/
@[expose] def wireParamSparseDepthSpace (M₀ : ℕ) : ℕ :=
  let E := (M₀ ^ 2 + 2).size
  let q := 38 * (2 ^ 24 * E) ^ 8 + E
  let P := 4 * (q + E + 10)
  let L := P + E + 4
  L + L + Num.logarithmSpace L P E

/-- Total heap space bound `paramSpace` for `wireParamModule`. -/
@[expose] def wireParamSpace (decK decThr witnessDen : ℕ) (pds : Spanner.PathDSParams) (M₀ : ℕ) : ℕ :=
  let den := Expander.maxPhiDenOf decK decThr (M₀ ^ 2)
  let cap := 36 * M₀ ^ 2 * den + 1
  7 + (M₀ + 2).size + wireParamChainDepthSpace M₀ + wireParamSparseDepthSpace M₀ +
    pds.boundsSpace den (M₀ ^ 2) + pds.boundsSpace witnessDen cap

/-- Step-cost bound for `prepareSolverChainWithDepthWorkspace` at `M₀, d`. -/
@[expose] def wireParamChainDepthCost (M₀ d : ℕ) : ℕ :=
  let E := (M₀ + 2).size
  let q := 38 * (2 ^ 48 * E) ^ 8 + E
  let P := 4 * (q + E + 10)
  let L := P + E + 4
  71 * L + Num.logarithmCost L P E + 14 * E + (19 * d + 32) * M₀.size + 310 * (d - 1) + 537

/-- Step-cost bound for `prepareSolverSparseCoreWithDepthWorkspace` at `M₀, L_sp`. -/
@[expose] def wireParamSparseDepthCost (M₀ L_sp : ℕ) : ℕ :=
  let E := (M₀ ^ 2 + 2).size
  let q := 38 * (2 ^ 24 * E) ^ 8 + E
  let P := 4 * (q + E + 10)
  let L := P + E + 4
  71 * L + Num.logarithmCost L P E + 14 * E + 166 * (L_sp - 1) + 368

/-- Total step-cost bound `paramCost` for `wireParamModule`. -/
@[expose] def wireParamCost (decK decThr witnessDen : ℕ) (pds : Spanner.PathDSParams)
    (entries : List (ℕ × ℕ × List ℕ)) (m V M₀ d L_sp : ℕ) : ℕ :=
  lookupEntriesCost entries + scalarParamsCost m V M₀ +
    wireParamChainDepthCost M₀ d + wireParamSparseDepthCost M₀ L_sp +
    gammaAndLevelsCost decK decThr witnessDen M₀ L_sp d pds.K_bounds + 20

private def dummyInstanceOfM (m : ℕ) : Instance where
  n := 1
  edges := List.replicate m ⟨0, 0, 0, 0, 0⟩
  demand := []

private lemma dummyInstanceOfM_m (m : ℕ) : (dummyInstanceOfM m).m = m := by
  simp [dummyInstanceOfM, Instance.m]

private lemma hasAt_wireParamModule {b threshold A decK decThr witnessDen : ℕ}
    {boundsProcs : ℕ → List Stmt} {entries : List (ℕ × ℕ × List ℕ)} {p : Program}
    (hp : p.HasAt b (wireParamModule b threshold A decK decThr witnessDen boundsProcs entries)) :
    p.procs[b]? = some (wireParamEntryBody (b + 1) (b + wireParamClogOff) (b + wireParamBoundsOff)
        threshold A decK decThr witnessDen entries) ∧
    p.HasAt (b + 1) (initDepthProcedures (b + 1) 4) ∧
    p.HasAt (b + wireParamClogOff) (Scaling.Machine.clogTwoModule (b + wireParamClogOff)) ∧
    p.HasAt (b + wireParamBoundsOff) (boundsProcs (b + wireParamBoundsOff)) := by
  unfold wireParamModule at hp
  have h123 := Num.hasAt_append_left hp
  have hb := Num.hasAt_append_right hp
  have h12 := Num.hasAt_append_left h123
  have hclog := Num.hasAt_append_right h123
  have h1 := Num.hasAt_append_left h12
  have hdepth := Num.hasAt_append_right h12
  have hlen12 : ([wireParamEntryBody (b + 1) (b + wireParamClogOff) (b + wireParamBoundsOff)
      threshold A decK decThr witnessDen entries] ++ initDepthProcedures (b + 1) 4).length =
      wireParamClogOff := by
    simp [wireParamClogOff, initDepthProcedures_length_eq]; omega
  have hlen123 : ([wireParamEntryBody (b + 1) (b + wireParamClogOff) (b + wireParamBoundsOff)
      threshold A decK decThr witnessDen entries] ++ initDepthProcedures (b + 1) 4 ++
      Scaling.Machine.clogTwoModule (b + wireParamClogOff)).length = wireParamBoundsOff := by
    simp [wireParamBoundsOff, wireParamClogOff, initDepthProcedures_length_eq,
      Scaling.Machine.clogTwoModule]; omega
  refine ⟨h1.head, by simpa using hdepth, ?_, ?_⟩
  · simpa only [hlen12] using hclog
  · simpa only [hlen123] using hb

/-- **Hit branch**: if `(m, V, [d, branch, psi, quality, epsExp, N₀] ++ (range d).map lvlM ++
[coreDepth])` is in `entries` (with unique key `(m, V)`), `wireParamModule` meets
`initParamSetupContract` in space `wireParamSpace` and time `wireParamCost`. -/
theorem wireParamModule_meetsContract_hit
    {w b threshold A decK decThr witnessDen m V L_in P_in d branch psi quality epsExp N₀
      coreDepth : ℕ}
    {lvlM : ℕ → ℕ} {pds : Spanner.PathDSParams}
    {boundsProcs : ℕ → List Stmt} {entries : List (ℕ × ℕ × List ℕ)} {p : Program}
    (hp : p.HasAt b (wireParamModule b threshold A decK decThr witnessDen boundsProcs entries))
    (_hM01 : 1 ≤ max m threshold) (hdLe : d ≤ (max m threshold + 2).size)
    (hw2 : 2 < 2 ^ w) (hmW : m < 2 ^ w) (hVW : V < 2 ^ w)
    (hdW : d < 2 ^ w) (hbrW : branch < 2 ^ w) (hpsiW : psi < 2 ^ w)
    (hqW : quality < 2 ^ w) (hepsW : epsExp < 2 ^ w) (hNW : N₀ < 2 ^ w)
    (hMW : ∀ i < d, lvlM i < 2 ^ w) (hcDW : coreDepth < 2 ^ w)
    (hmem : (m, V, [d, branch, psi, quality, epsExp, N₀] ++ (List.range d).map lvlM ++
      [coreDepth]) ∈ entries)
    (huniq : ∀ e ∈ entries, e.1 = m → e.2.1 = V →
      e.2.2 = [d, branch, psi, quality, epsExp, N₀] ++ (List.range d).map lvlM ++ [coreDepth]) :
    let M₀ := max m threshold
    MeetsContract w p b
      (initParamSetupContract w m V L_in P_in d branch psi quality epsExp N₀ coreDepth lvlM
        (wireParamSpace decK decThr witnessDen pds M₀)
        (wireParamCost decK decThr witnessDen pds entries m V M₀ d (Expander.chosenL (M₀ ^ 2)))) := by
  intro M₀
  have hAt := hasAt_wireParamModule hp
  apply meetsContract_of_runs hAt.1
  intro args mem pos ω _ hpre
  obtain ⟨heap, rfl, hz, hroom⟩ := hpre
  let xs : List ℕ := [d, branch, psi, quality, epsExp, N₀] ++ (List.range d).map lvlM ++
    [coreDepth]
  have hlen : xs.length = 7 + d := by simp [xs]; omega
  have hxsW : ∀ x ∈ xs, x < 2 ^ w := by
    intro x hx
    simp only [xs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range] at hx
    rcases hx with ((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | rfl
    · exact hdW
    · exact hbrW
    · exact hpsiW
    · exact hqW
    · exact hepsW
    · exact hNW
    · exact hMW i hi
    · exact hcDW
  have h6dLe : 7 + d ≤ wireParamSpace decK decThr witnessDen pds M₀ := by
    change d ≤ (M₀ + 2).size at hdLe
    unfold wireParamSpace; dsimp only; omega
  have hroomXs : heap + xs.length < 2 ^ w := by rw [hlen]; omega
  obtain ⟨out, c1, hr1, hlist1, hframe1, hc1⟩ :=
    lookupEntries_runs_hit (w := w) (m := m) (V := V) (heap := heap) (xs := xs) (p := p) (ω := ω)
      entries (startState [m, V, L_in, P_in, heap] mem pos)
      hw2 rfl rfl rfl hmW hVW hmem huniq hxsW hroomXs
  refine ⟨.returned (heap + xs.length), out, c1 + 1,
    runs_seq_iff.mpr (Or.inl ⟨heap + xs.length, c1, hr1, rfl, rfl⟩), ?_, ?_⟩
  · dsimp only [initParamSetupContract, Outcome.value]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some]
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have hj' : j < xs.length := by rw [hlen]; simp at hj; omega
      have hget : xs[j]'hj' = ([d, branch, psi, quality, epsExp, N₀] : List ℕ)[j] := by
        simp only [xs]
        rw [List.getElem_append_left (by simp at hj ⊢; omega)]
        exact List.getElem_append_left (by simpa using hj)
      simpa [hget] using hlist1 j hj'
    · intro i hi
      have hi' : 6 + i < xs.length := by rw [hlen]; omega
      have hget : xs[6 + i]'hi' = lvlM i := by
        simp only [xs]
        rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
        simp
      simpa [Nat.add_assoc, hget] using hlist1 (6 + i) hi'
    · have hi' : 6 + d < xs.length := by rw [hlen]; omega
      have hget : xs[6 + d]'hi' = coreDepth := by
        simp only [xs]
        rw [List.getElem_append_right (by simp only [List.length_append, List.length_cons,
          List.length_nil, List.length_map, List.length_range]; omega)]
        simp
      simpa [Nat.add_assoc, hget] using hlist1 (6 + d) hi'
    · intro a ha
      exact hframe1 a (Or.inl ha)
    · intro a ha
      exact (hframe1 a (Or.inr ha)).trans (hz a (by omega))
  · change c1 + 1 ≤ wireParamCost decK decThr witnessDen pds entries m V M₀ d (Expander.chosenL (M₀ ^ 2))
    unfold wireParamCost; omega

/-- **General branch**: when `(m, V)` misses `entries` and `lvlM i` equals the exact integer
formula `(M₀ * γ^(i+1) + branch^i - 1) / branch^i`, `wireParamModule` meets
`initParamSetupContract` in space `wireParamSpace` and time `wireParamCost`. -/
theorem wireParamModule_meetsContract_general
    {w b threshold A decK decThr witnessDen m V L_in P_in : ℕ}
    {lvlM : ℕ → ℕ} {pds : Spanner.PathDSParams}
    {boundsProcs : ℕ → List Stmt} {entries : List (ℕ × ℕ × List ℕ)} {p : Program}
    (hp : p.HasAt b (wireParamModule b threshold A decK decThr witnessDen boundsProcs entries))
    (hboundsSpec : p.HasAt (b + wireParamBoundsOff) (boundsProcs (b + wireParamBoundsOff)) →
      MeetsContract w p (b + wireParamBoundsOff) (Spanner.pathDSBoundsContract pds w))
    (hdecK : 1 ≤ decK) (hwit1 : 1 ≤ witnessDen)
    (hM01 : 1 ≤ max m threshold) (hw14 : 14 ≤ w) (h220000W : 220000 < 2 ^ w)
    (hmiss : ∀ e ∈ entries, m ≠ e.1 ∨ V ≠ e.2.1)
    (hmW : m < 2 ^ w) (hVW : V < 2 ^ w) (hthrW : threshold < 2 ^ w)
    (hM0_2W : max m threshold + 2 < 2 ^ w) (hN0W : 4 * max m threshold < 2 ^ w)
    (hqualW : paramQuality threshold A m < 2 ^ w)
    (halphaScaleW : Num.IPM.alphaScale m V + 1 < 2 ^ w)
    (hepsW : paramEpsExp threshold A m V < 2 ^ w)
    (hpsiW : paramPsi threshold A m V < 2 ^ w)
    (h4M2W : 4 * max m threshold ^ 2 + 2 < 2 ^ w)
    (hcubeW : (Nat.log 2 (4 * max m threshold ^ 2 + 2) + 2) ^ 3 < 2 ^ w)
    (hdenW : Expander.maxPhiDenOf decK decThr (max m threshold ^ 2) < 2 ^ w)
    (hcapW : 36 * max m threshold ^ 2 * Expander.maxPhiDenOf decK decThr (max m threshold ^ 2) + 1 < 2 ^ w)
    (hwitW : witnessDen < 2 ^ w)
    (hcw1 : pds.cw * (Nat.log 2 (Expander.maxPhiDenOf decK decThr (max m threshold ^ 2) +
        max m threshold ^ 2 +
        pds.gExp (Expander.maxPhiDenOf decK decThr (max m threshold ^ 2)) (max m threshold ^ 2) +
        pds.gDel (Expander.maxPhiDenOf decK decThr (max m threshold ^ 2)) (max m threshold ^ 2) + 2) + 1) ≤ w)
    (hcw2 : pds.cw * (Nat.log 2 (witnessDen +
        (36 * max m threshold ^ 2 * Expander.maxPhiDenOf decK decThr (max m threshold ^ 2) + 1) +
        pds.gExp witnessDen (36 * max m threshold ^ 2 * Expander.maxPhiDenOf decK decThr (max m threshold ^ 2) + 1) +
        pds.gDel witnessDen (36 * max m threshold ^ 2 * Expander.maxPhiDenOf decK decThr (max m threshold ^ 2) + 1) + 2) + 1) ≤ w)
    (hnumW : ∀ i < (Chain.concreteChainParams (max m threshold) hM01).d,
      let M₀ := max m threshold
      let C := Chain.concreteChainParams M₀ hM01
      let L_sp := Expander.chosenL (M₀ ^ 2)
      let den := Expander.maxPhiDenOf decK decThr (M₀ ^ 2)
      let cap := 36 * M₀ ^ 2 * den + 1
      let g := (max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap)) ^ 2
      let γ := 3 ^ L_sp * g ^ (L_sp + 1)
      M₀ * γ ^ (i + 1) + C.k ^ i < 2 ^ w)
    (hlvlM : ∀ i < (Chain.concreteChainParams (max m threshold) hM01).d,
      let M₀ := max m threshold
      let C := Chain.concreteChainParams M₀ hM01
      let L_sp := Expander.chosenL (M₀ ^ 2)
      let den := Expander.maxPhiDenOf decK decThr (M₀ ^ 2)
      let cap := 36 * M₀ ^ 2 * den + 1
      let g := (max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap)) ^ 2
      let γ := 3 ^ L_sp * g ^ (L_sp + 1)
      lvlM i = (M₀ * γ ^ (i + 1) + C.k ^ i - 1) / C.k ^ i) :
    let M₀ := max m threshold
    let C := Chain.concreteChainParams M₀ hM01
    MeetsContract w p b
      (initParamSetupContract w m V L_in P_in C.d C.k
        (paramPsi threshold A m V) (paramQuality threshold A m)
        (paramEpsExp threshold A m V) (paramN0 threshold m) (Expander.chosenL (M₀ ^ 2)) lvlM
        (wireParamSpace decK decThr witnessDen pds M₀)
        (wireParamCost decK decThr witnessDen pds entries m V M₀ C.d (Expander.chosenL (M₀ ^ 2)))) := by
  intro M₀ C
  obtain ⟨hEntry, hDepthAt, hClogAt, hBoundsAt⟩ := hasAt_wireParamModule hp
  have hDepthC := initDepthProcedures_meetsContracts (w := w) (by decide : 0 < 4) (by omega) hDepthAt
  have hClogC := Scaling.Machine.clogTwo_meetsContract (w := w) hClogAt (Num.IPM.alphaScale m V)
  have hBoundsC := hboundsSpec hBoundsAt
  have hw2 : 2 < 2 ^ w := by
    have h1 : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  apply meetsContract_of_runs hEntry
  intro args mem pos ω _ hpre
  obtain ⟨heap, rfl, hz, hroom⟩ := hpre
  let st0 := startState [m, V, L_in, P_in, heap] mem pos
  -- Step 1: lookupEntries misses
  obtain ⟨s1, c1, hr1, hm1, _, hkeep1, hc1⟩ :=
    lookupEntries_runs_miss (w := w) (m := m) (V := V) (p := p) (ω := ω)
      entries st0 hw2 rfl rfl hmW hVW hmiss
  -- Step 2: computeScalarParamsStmt
  have hscrW : heap + 6 + (M₀ + 2).size < 2 ^ w := by
    unfold wireParamSpace at hroom; dsimp only at hroom; omega
  obtain ⟨s2, c2, hr2, hs2_0, hs2_22, _, _, hs2_82, hs2_83, hs2_84, hs2_85, hs2_86, hs2_98, hm2, hc2⟩ :=
    computeScalarParamsStmt_runs (w := w) (p := p) (ω := ω) hDepthC.1 hClogC
      ((hkeep1 0 (by decide) (by decide)).trans rfl)
      ((hkeep1 1 (by decide) (by decide)).trans rfl)
      ((hkeep1 4 (by decide) (by decide)).trans rfl)
      hmW hVW hthrW hM0_2W hN0W hqualW halphaScaleW hepsW hpsiW hscrW h220000W
  -- Step 3: prepareSolverChainWithDepthWorkspace
  let scr0 := heap + 6 + (M₀ + 2).size
  have hzScr0 : ZeroFrom s2.mem scr0 := fun a ha => by
    rw [hm2, hm1]; exact hz a (by omega)
  have hroomD : scr0 + wireParamChainDepthSpace M₀ < 2 ^ w := by
    unfold wireParamSpace at hroom; dsimp only at hroom; omega
  have hM0_dummy : max (dummyInstanceOfM m).m threshold = M₀ := by
    rw [dummyInstanceOfM_m]
  have hroomD_exp :
      let E := (max (dummyInstanceOfM m).m threshold + 2).size
      let q := 38 * (2 ^ 48 * E) ^ 8 + E
      let P := 4 * (q + E + 10)
      let L := P + E + 4
      scr0 + L + L + Num.logarithmSpace L P E < 2 ^ w := by
    dsimp only; rw [hM0_dummy]
    unfold wireParamChainDepthSpace at hroomD; dsimp only at hroomD; omega
  obtain ⟨s3, c3, ret3, hr3, hs3_22, hs3_75, hs3_76, hs3_98, hscr0_le, _, hret3_le,
      hframe3, hz3, hkeep3, hc3⟩ :=
    prepareSolverChainWithLinkedDepth_runs (w := w) (threshold := threshold) (b := b + 1) (h := 4)
      (a := scr0) (dummyInstanceOfM m) (p := p) (ω := ω) (st := s2) (retry := .nop)
      (by omega) hDepthAt (by simpa [IPM.namedInstance, MGraph.m, dummyInstanceOfM_m] using hs2_0)
      (by decide) hs2_98 hzScr0
      (by rwa [hM0_dummy]) (by rwa [hM0_dummy]) hroomD_exp
  simp only [hM0_dummy] at hs3_22 hs3_75 hs3_76 hret3_le hc3
  have hret3_le' : ret3 ≤ scr0 + wireParamChainDepthSpace M₀ := by
    unfold wireParamChainDepthSpace; dsimp only; omega
  -- Step 4: prepareSolverSparseCoreWithDepthWorkspace
  have hroomS : ret3 + wireParamSparseDepthSpace M₀ < 2 ^ w := by
    have hroom' := hroom
    unfold wireParamSpace at hroom'; dsimp only at hroom'; omega
  have hroomS_exp :
      let E := (M₀ ^ 2 + 2).size
      let q := 38 * (2 ^ 24 * E) ^ 8 + E
      let P := 4 * (q + E + 10)
      let L := P + E + 4
      ret3 + L + L + Num.logarithmSpace L P E < 2 ^ w := by
    dsimp only
    unfold wireParamSparseDepthSpace at hroomS; dsimp only at hroomS; omega
  have hM2_2W : M₀ ^ 2 + 2 < 2 ^ w := by
    have h4 : 4 * M₀ ^ 2 + 2 < 2 ^ w := h4M2W
    omega
  obtain ⟨s4, c4, ret4, hr4, hs4_23, hs4_44, hs4_98, hret3_le4, _, hret4_le,
      hframe4, hz4, hkeep4, _, hc4⟩ :=
    prepareSolverSparseCoreWithLinkedDepth_runs (w := w) (h := 4) (b := b + 1) (a := ret3) (M := M₀)
      (p := p) (ω := ω) (st := s3) (retry := .nop)
      (by omega) hDepthAt hs3_22 hM01 hM2_2W (by decide) hs3_98 hz3 hroomS_exp
  have hret4_le' : ret4 ≤ ret3 + wireParamSparseDepthSpace M₀ := by
    unfold wireParamSparseDepthSpace; dsimp only; omega
  -- Step 5: computeGammaAndLevelsStmt
  have hdLe : C.d ≤ (M₀ + 2).size := chosenD_le_size_add_two hM01
  have hRoomB : ret4 + pds.boundsSpace (Expander.maxPhiDenOf decK decThr (M₀ ^ 2)) (M₀ ^ 2) +
      pds.boundsSpace witnessDen (36 * M₀ ^ 2 * Expander.maxPhiDenOf decK decThr (M₀ ^ 2) + 1) < 2 ^ w := by
    have hroom' := hroom
    unfold wireParamSpace at hroom'; dsimp only at hroom'; omega
  obtain ⟨s5, ret5, c5, hr5, hret4_le5, hret5_le, hlist5, hlvl5, hdepth5, hframe5, hz5, hc5⟩ :=
    computeGammaAndLevelsStmt_runs (w := w) (decK := decK) (decThr := decThr)
      (witnessDen := witnessDen) (boundsProc := b + wireParamBoundsOff)
      (M₀ := M₀) (L := Expander.chosenL (M₀ ^ 2)) (d := C.d) (branch := C.k)
      (heap := heap) (quality := paramQuality threshold A m)
      (epsExp := paramEpsExp threshold A m V) (psi := paramPsi threshold A m V)
      (N₀ := paramN0 threshold m) (s2 := ret4) (pds := pds) (p := p) (ω := ω) (st := s4)
      hdecK hwit1 hM01 C.hd C.hk hBoundsC
      ((hkeep4 22 (by omega) (by decide) (by decide)).trans hs3_22)
      hs4_23 hs4_44
      ((hkeep4 75 (by omega) (by decide) (by decide)).trans hs3_75)
      ((hkeep4 76 (by omega) (by decide) (by decide)).trans hs3_76)
      ((hkeep4 82 (by omega) (by decide) (by decide)).trans ((hkeep3 82 (by omega) (by decide) (by decide) (by decide)).trans hs2_82))
      ((hkeep4 83 (by omega) (by decide) (by decide)).trans ((hkeep3 83 (by omega) (by decide) (by decide) (by decide)).trans hs2_83))
      ((hkeep4 84 (by omega) (by decide) (by decide)).trans ((hkeep3 84 (by omega) (by decide) (by decide) (by decide)).trans hs2_84))
      ((hkeep4 85 (by omega) (by decide) (by decide)).trans ((hkeep3 85 (by omega) (by decide) (by decide) (by decide)).trans hs2_85))
      ((hkeep4 86 (by omega) (by decide) (by decide)).trans ((hkeep3 86 (by omega) (by decide) (by decide) (by decide)).trans hs2_86))
      hs4_98 (by omega) hz4 h4M2W hcubeW hdenW hcapW hwitW hRoomB hcw1 hcw2 hnumW
  have rFull : Runs w p ω
      (wireParamEntryBody (b + 1) (b + wireParamClogOff) (b + wireParamBoundsOff)
        threshold A decK decThr witnessDen entries)
      st0 (.returned ret5) s5 (c1 + (c2 + (c3 + (c4 + c5 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, hr1,
    runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, hr2,
    runs_seq_iff.mpr (Or.inr ⟨s3, c3, _, hr3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, c5, hr4, hr5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨.returned ret5, s5, _, rFull, ?_, ?_⟩
  · dsimp only [initParamSetupContract, Outcome.value]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some]
    refine ⟨by omega, ?_, hlist5, ?_, hdepth5, ?_, hz5⟩
    · unfold wireParamSpace; dsimp only; omega
    · intro i hi
      rw [hlvl5 i hi, hlvlM i hi]
    · intro a ha
      rw [hframe5 a ha, hframe4 a (by omega), hframe3 a (by omega), hm2, hm1]; rfl
  · change c1 + (c2 + (c3 + (c4 + c5 + 1) + 1) + 1) + 1 ≤
      wireParamCost decK decThr witnessDen pds entries m V M₀ C.d (Expander.chosenL (M₀ ^ 2))
    have hc2' : c2 ≤ scalarParamsCost m V M₀ := hc2
    have hc3' : c3 ≤ wireParamChainDepthCost M₀ C.d := hc3
    have hc4' : c4 ≤ wireParamSparseDepthCost M₀ (Expander.chosenL (M₀ ^ 2)) := hc4
    unfold wireParamCost
    omega

end MinCostFlow.MinRatio

end
