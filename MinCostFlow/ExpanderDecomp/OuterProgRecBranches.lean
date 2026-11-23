module

public import MinCostFlow.ExpanderDecomp.OuterProgRecBase
import all MinCostFlow.ExpanderDecomp.ProgCompLabels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Recursive Outer Decomposition Procedure and Branch Runners (`OuterProgRecBranches`)

Defines the deterministic (`NoRand`) recursive outer expander decomposition procedure
`outerDecompRecProc`, its bundled environment `RecGlobalEnv`, subprocedure
contracts `RecSubprocs`, per-edge/per-witness space and step budgets (`recPerEdgeSpace`,
`recPerWitSpace`, `recPerEdgeCost`, `recPerWitCost`), and the four factored branch execution
lemmas (`recBase_runs`, `recPortGame_runs`, `recCut_runs`, `recWitness_runs`) composed by
strong induction in `OuterProgRec.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 1. Procedure Definition and `NoRand` -/

/-- Base branch (`e ≤ QOut`): compute connected-component labels inside `H` via `idx.bComp`,
write shifted labels into `labelsAddr` and advance `nextLblAddr`, return `h + 4 * k + 6 * e + 3`.
Reads `r0=k, r1=vertsAddr, r2=e, r3=edgesAddr, r5=locAddr, r6=labelsAddr, r7=nextLblAddr, r8=h`. -/
def recBaseStmt (idx : OuterRecIndices) : Stmt :=
  .assign 10 (.reg 8) ;;
  .assign 11 (.bin .add (.reg 8) (.reg 0)) ;;
  .call 12 idx.bComp [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 10, .reg 11] ;;
  writeCompLabelsStmt ;;
  .assign 12 (.bin .add (.reg 8) (.bin .mul (.const 4) (.reg 0))) ;;
  .assign 12 (.bin .add (.reg 12) (.bin .mul (.const 6) (.reg 2))) ;;
  .ret (.bin .add (.reg 12) (.const 3))

/-- Recursive prefix (`QOut < e`): build `portGraph cloud G X` + `portOwner` via `idx.bPort`,
then run `outerGameProc` via `idx.bGame`. Leaves `r10=ownerAddr, r11=pgAddr, r14=outResAddr,
r15=h3, r16=mem[outResAddr]`. -/
def recPortGameStmt (idx : OuterRecIndices) : Stmt :=
  .assign 10 (.reg 8) ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 2))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 20) (.reg 2))) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 0))) ;;
  .assign 13 (.bin .add (.reg 13) (.bin .mul (.const 20) (.reg 2))) ;;
  .assign 13 (.bin .add (.reg 13) (.const 4)) ;;
  .call 13 idx.bPort [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 10, .reg 11, .reg 12, .reg 13] ;;
  .assign 14 (.reg 13) ;;
  .assign 15 (.bin .add (.reg 13) (.const 4)) ;;
  .call 15 idx.bGame [.reg 2, .reg 11, .reg 4, .reg 14, .reg 15] ;;
  .assign 16 (.load (.reg 14))

/-- Cut branch (`tag = 0`): round port cut via `idx.bRound`, restrict/strip/recurse on `S`,
then restrict/strip/recurse on `T`, returning the final zero-heap cursor. -/
def recCutStmt (idx : OuterRecIndices) : Stmt :=
  (.assign 17 (.load (.bin .add (.reg 14) (.const 1))) ;;
   .assign 18 (.load (.bin .add (.reg 14) (.const 2))) ;;
   .assign 19 (.reg 15) ;;
   .assign 20 (.bin .add (.reg 19) (.reg 0))) ;;
  (.assign 21 (.bin .add (.reg 20) (.reg 0)) ;;
   .assign 22 (.bin .add (.reg 21) (.const 2)) ;;
   .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 2))) ;;
   .assign 24 (.bin .add (.reg 23) (.bin .mul (.const 2) (.reg 2)))) ;;
  (.assign 25 (.bin .add (.reg 24) (.reg 0)) ;;
   .assign 26 (.bin .add (.reg 25) (.reg 0))) ;;
  .call 26 idx.bRound
    [.reg 0, .reg 1, .reg 2, .reg 10, .reg 17, .reg 18, .reg 5, .reg 19, .reg 20, .reg 21, .reg 26] ;;
  (.assign 27 (.load (.reg 21)) ;;
   .assign 28 (.load (.bin .add (.reg 21) (.const 1)))) ;;
  .call 29 idx.bRestrict [.reg 27, .reg 19, .reg 2, .reg 3, .reg 5, .reg 22] ;;
  .call 30 idx.bStripIso [.reg 27, .reg 19, .reg 29, .reg 22, .reg 5, .reg 6, .reg 7, .reg 24] ;;
  .call 26 idx.bSelf [.reg 30, .reg 24, .reg 29, .reg 22, .reg 4, .reg 5, .reg 6, .reg 7, .reg 26] ;;
  .call 29 idx.bRestrict [.reg 28, .reg 20, .reg 2, .reg 3, .reg 5, .reg 23] ;;
  .call 30 idx.bStripIso [.reg 28, .reg 20, .reg 29, .reg 23, .reg 5, .reg 6, .reg 7, .reg 25] ;;
  .call 26 idx.bSelf [.reg 30, .reg 25, .reg 29, .reg 23, .reg 4, .reg 5, .reg 6, .reg 7, .reg 26] ;;
  .ret (.reg 26)

/-- Witness branch (`tag = 1`): contract fake edges via `idx.bContract`, prune via `idx.bRF`,
paint `R` with one fresh label, compute `X \ R` via `idx.bSetDiff`, restrict/strip/recurse on
`actRest`, returning the final zero-heap cursor. -/
def recWitnessStmt (idx : OuterRecIndices) : Stmt :=
  (.assign 17 (.load (.bin .add (.reg 14) (.const 2))) ;;
   .assign 18 (.load (.bin .add (.reg 14) (.const 3))) ;;
   .assign 22 (.load (.bin .add (.reg 4) (.const 8))) ;;
   .assign 23 (.load (.bin .add (.reg 4) (.const 4)))) ;;
  (.assign 19 (.reg 15) ;;
   .assign 20 (.bin .add (.reg 19) (.bin .mul (.const 2) (.reg 17))) ;;
   .assign 24 (.bin .add (.reg 20) (.const 2)) ;;
   .assign 25 (.bin .add (.reg 24) (.reg 0))) ;;
  (.assign 26 (.bin .add (.reg 25) (.reg 0)) ;;
   .assign 29 (.bin .add (.reg 26) (.bin .mul (.const 2) (.reg 2))) ;;
   .assign 33 (.bin .add (.reg 29) (.reg 0))) ;;
  (.store (.reg 20) (.const 1) ;;
   .store (.bin .add (.reg 20) (.const 1)) (.reg 22)) ;;
  .call 27 idx.bContract [.reg 10, .reg 17, .reg 18, .reg 19] ;;
  computeRfWorkBoundStmt ;;
  .assign 34 (.bin .add (.reg 33) (.reg 31)) ;;
  .call 28 idx.bRF [.reg 0, .reg 1, .reg 2, .reg 3, .reg 27, .reg 19, .reg 20, .reg 5, .reg 24, .reg 33] ;;
  writeConstLabelStmt ;;
  .call 30 idx.bSetDiff [.reg 0, .reg 1, .reg 28, .reg 24, .reg 5, .reg 25] ;;
  .call 31 idx.bRestrict [.reg 30, .reg 25, .reg 2, .reg 3, .reg 5, .reg 26] ;;
  .call 32 idx.bStripIso [.reg 30, .reg 25, .reg 31, .reg 26, .reg 5, .reg 6, .reg 7, .reg 29] ;;
  .call 34 idx.bSelf [.reg 32, .reg 29, .reg 31, .reg 26, .reg 4, .reg 5, .reg 6, .reg 7, .reg 34] ;;
  .ret (.reg 34)

/-- Complete recursive outer expander decomposition procedure.
Args: `[k, vertsAddr, e, edgesAddr, paramAddr, locAddr, labelsAddr, nextLblAddr, h]`. -/
def outerDecompRecProc (idx : OuterRecIndices) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 4) (.const 10))) ;;
  .cond (.bin .lt (.reg 9) (.reg 2))
    (recPortGameStmt idx ;;
     .cond (.reg 16) (recWitnessStmt idx) (recCutStmt idx))
    (recBaseStmt idx)

/-! ## 2. Per-Edge and Per-Witness Space / Step Budgets -/

/-- Pure model per-edge cost factor from `OuterCost.lean`. -/
def modelPerEdge (cfg : ParamConfig) (M r routeC : ℕ) : ℕ :=
  2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
    routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3 +
    232 * LParam M

/-- Per-edge zero-heap space budget for one recursion node (words per edge of `H`). -/
def recPerEdgeSpace (cfg : ParamConfig) (C_sp M r routeC : ℕ) : ℕ :=
  C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * LParam M + 1)) +
    (49 * LParam M + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10) +
    41600 * (M + 1) ^ 4 + 300 * LParam M + 300

/-- Per-witness-edge zero-heap space budget (words per edge of a witness node `H`, also dominating
the arithmetic headroom in `PruneWordBound`). -/
def recPerWitSpace (cfg : ParamConfig) (M r : ℕ) : ℕ :=
  400 * Lambda cfg M r * LParam M + 400

/-- Per-edge Word-RAM step budget for one recursion node. -/
def recPerEdgeCost (cfg : ParamConfig) (C_core C_rt M r routeC : ℕ) : ℕ :=
  outerGameCostFactor C_core C_rt * (modelPerEdge cfg M r routeC + 2) +
    (runnerScale explicitProgram * 760 + 8000) + 40 * r

/-- Per-witness-edge Word-RAM step budget (dominates `ProgRemoveFake.removeFakeCost`). -/
def recPerWitCost (cfg : ParamConfig) (M r : ℕ) : ℕ :=
  2 ^ 30 * (Lambda cfg M r) ^ 2 * (LParam M) ^ 2 + 2000

/-! ## 3. Global Environment and Subprocedure Bundles -/

/-- Read-only global context fixed across all recursive calls of `outerDecompRecProc`. -/
structure RecGlobalEnv (cfg : ParamConfig) (M r w : ℕ) (G : Graph)
    (paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ) : Prop where
  hA60 : 60 ≤ cfg.A
  hα : (1 : ℝ) / (cfg.a₀ : ℝ) ≤ cloudAlpha
  hv : G.IsValid
  hr1 : 1 ≤ r
  hrl : r ≤ ell M
  hM_eq : M = G.m
  hN2 : 2 ≤ NOf M r
  h2M_pow : 2 * M ≤ (NOf M r) ^ r
  h2M_L : 2 * M < 2 ^ LParam M
  hparH : paramAddr + 12 ≤ hRoot
  hlocH : locAddr + G.n ≤ hRoot
  hlblH : labelsAddr + G.n ≤ hRoot
  hnextH : nextLblAddr + 1 ≤ hRoot
  hdPL : DisjointRange paramAddr 12 locAddr G.n
  hdPLb : DisjointRange paramAddr 12 labelsAddr G.n
  hdPN : DisjointRange paramAddr 12 nextLblAddr 1
  hdLLb : DisjointRange locAddr G.n labelsAddr G.n
  hdLN : DisjointRange locAddr G.n nextLblAddr 1
  hdLbN : DisjointRange labelsAddr G.n nextLblAddr 1
  hN2M_w : NOf M r * (2 * M) + 16 < 2 ^ w
  hwb : bOut cfg M < 2 ^ w
  hwM : M < 2 ^ w
  hwR : r < 2 ^ w
  hwN : G.n + 16 < 2 ^ w
  hw250 : 250 < 2 ^ w

/-- Bundled `MeetsContract` hypotheses for `outerDecompRecProc`. -/
structure RecSubprocs (M r w : ℕ) (p : Program) (idx : OuterRecIndices)
    (C_core C_rt C_sp routeC : ℕ) : Prop where
  hSelf : p.procs[idx.bSelf]? = some (outerDecompRecProc idx)
  hComp : MeetsContract w p idx.bComp (compLabelsInContract w)
  hPort : MeetsContract w p idx.bPort (portGraphContract w)
  hGame : MeetsContract w p idx.bGame (outerGameContract M r C_core C_rt C_sp routeC w)
  hRound : MeetsContract w p idx.bRound (outerRoundPortCutContract w)
  hRestrict : MeetsContract w p idx.bRestrict (restrictContract w)
  hStripIso : MeetsContract w p idx.bStripIso (stripIsolatedContract w)
  hContract : MeetsContract w p idx.bContract (outerContractEdgesContract w)
  hRF : MeetsContract w p idx.bRF (removeFakeContract w)
  hSetDiff : MeetsContract w p idx.bSetDiff (setDiffContract w)

/-- Recursive call postcondition asserted at each node `H` of the strong induction. -/
def RecNodePost (cfg : ParamConfig) (M r C_core C_rt C_sp routeC : ℕ)
    (G : Graph) (locAddr labelsAddr nextLblAddr h : ℕ)
    (H : CompactSubgraph) (mem₀ : ℕ → ℕ) (nl₀ : ℕ) (h' : ℕ) (mem' : ℕ → ℕ) (c : ℕ) : Prop :=
  ∃ o : OuterRecOut,
    OuterRecSpec cfg M r G H o ∧
    LabelsMatchParts mem' labelsAddr H.vertSet o.parts nl₀ (mem' nextLblAddr) ∧
    mem' nextLblAddr ≤ nl₀ + H.verts.length ∧
    h ≤ h' ∧
    h' ≤ h + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
      (recPerWitSpace cfg M r) H.edges.length ∧
    ZeroFrom mem' h' ∧
    (∀ u < G.n, mem' (locAddr + u) = 0) ∧
    (∀ a < h,
      (∀ u ∈ H.vertSet, a ≠ labelsAddr + u) →
      a ≠ nextLblAddr →
      mem' a = mem₀ a) ∧
    c ≤ o.edgeSum * recPerEdgeCost cfg C_core C_rt M r routeC +
      o.witnessEdgeSum * recPerWitCost cfg M r + 600

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 4. `NoRand` and Arithmetic Helpers -/

lemma outerDecompRecProc_noRand (idx : OuterRecIndices) : (outerDecompRecProc idx).NoRand := by
  simp [outerDecompRecProc, recBaseStmt, recPortGameStmt, recCutStmt, recWitnessStmt,
    writeCompLabelsStmt_noRand, writeConstLabelStmt_noRand, computeRfWorkBoundStmt_noRand,
    Stmt.NoRand]

lemma tParam_mul_div_DOut_le (cfg : ParamConfig) (hA60 : 60 ≤ cfg.A) (M r e : ℕ) :
    tParam M * (e / DOut cfg M r) ≤ e := by
  have htD : tParam M ≤ DOut cfg M r := by
    unfold DOut
    have hA : 1 ≤ cfg.A := by omega
    have hLam := one_le_Lambda cfg M r
    have hb := one_le_bOut cfg M
    have hfac : 1 ≤ 16 * cfg.A * Lambda cfg M r * bOut cfg M := by
      have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 hA) hLam) hb
      omega
    calc tParam M = tParam M * 1 := (Nat.mul_one _).symm
      _ ≤ tParam M * (16 * cfg.A * Lambda cfg M r * bOut cfg M) := Nat.mul_le_mul_left _ hfac
      _ = 16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M := by ring
  calc tParam M * (e / DOut cfg M r)
      ≤ DOut cfg M r * (e / DOut cfg M r) := Nat.mul_le_mul_right _ htD
    _ ≤ e := Nat.mul_div_le _ _

/-- Bound on `outerGameMaxCost` in terms of `e * modelPerEdge`. -/
lemma outerGameMaxCost_le_modelPerEdge {cfg : ParamConfig} {M r routeC e : ℕ}
    (he_pos : 1 ≤ e) :
    outerGameMaxCost cfg M r routeC e ≤ e * modelPerEdge cfg M r routeC := by
  unfold outerGameMaxCost outerGameRoundBudget
  have hL : 4 ≤ LParam M := four_le_LParam M
  have hb : 1 ≤ bOut cfg M := one_le_bOut cfg M
  have h49_le_t : 49 * LParam M + 1 ≤ tParam M := by unfold tParam; omega
  have h49_le_50 : 49 * LParam M + 1 ≤ 50 * LParam M := by omega
  have h49_le_t1 : 49 * LParam M + 1 ≤ tParam M + 1 := by omega
  have hcore_t : (49 * LParam M + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) ≤
      e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) := by
    calc (49 * LParam M + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10))
        ≤ (tParam M + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) :=
          Nat.mul_le_mul_right _ h49_le_t1
      _ = e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) := by ring
  have hrt_t : (49 * LParam M + 1) * (routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1)) ≤
      e * (routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by
    have hbL : 1 ≤ bOut cfg M * LParam M := Nat.mul_pos hb (by omega)
    have hd : dOut cfg M + 1 ≤ 321 * (bOut cfg M * LParam M) := by
      unfold dOut
      have : 320 * bOut cfg M * LParam M = 320 * (bOut cfg M * LParam M) := by ring
      omega
    have hR : ROut cfg M ≤ 160 * 321 * (bOut cfg M) ^ 2 * (LParam M) ^ 2 := by
      unfold ROut
      calc 160 * bOut cfg M * (dOut cfg M + 1) * LParam M
          ≤ 160 * bOut cfg M * (321 * (bOut cfg M * LParam M)) * LParam M :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
        _ = 160 * 321 * (bOut cfg M) ^ 2 * (LParam M) ^ 2 := by ring
    have hprod : (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1 ≤
        2 ^ 29 * e * (bOut cfg M) ^ 3 * (LParam M) ^ 3 := by
      have h1 : (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M ≤
          13 * 321 * 160 * 321 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by
        calc (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M
            ≤ (13 * e) * (321 * (bOut cfg M * LParam M)) *
                (160 * 321 * (bOut cfg M) ^ 2 * (LParam M) ^ 2) :=
              Nat.mul_le_mul (Nat.mul_le_mul (by omega) hd) hR
          _ = 13 * 321 * 160 * 321 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by ring
      have hpos : 1 ≤ e * (bOut cfg M) ^ 3 * (LParam M) ^ 3 :=
        Nat.mul_pos (Nat.mul_pos he_pos (Nat.pow_pos hb)) (Nat.pow_pos (by omega))
      have hc : 13 * 321 * 160 * 321 + 1 ≤ 2 ^ 29 := by decide
      have hring : 2 ^ 29 * e * (bOut cfg M) ^ 3 * (LParam M) ^ 3 =
          2 ^ 29 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by ring
      rw [hring]
      calc (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1
          ≤ 13 * 321 * 160 * 321 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) +
              1 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by omega
        _ = (13 * 321 * 160 * 321 + 1) * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by ring
        _ ≤ 2 ^ 29 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := Nat.mul_le_mul_right _ hc
    calc (49 * LParam M + 1) * (routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1))
        ≤ tParam M * (routeC * (2 ^ 29 * e * (bOut cfg M) ^ 3 * (LParam M) ^ 3)) :=
          Nat.mul_le_mul h49_le_t (Nat.mul_le_mul_left routeC hprod)
      _ = e * (routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by ring
  have hscan : (49 * LParam M + 1) * (4 * e) ≤ e * (232 * LParam M) := by
    calc (49 * LParam M + 1) * (4 * e)
        ≤ (50 * LParam M) * (4 * e) := Nat.mul_le_mul_right _ h49_le_50
      _ = e * (200 * LParam M) := by ring
      _ ≤ e * (232 * LParam M) := Nat.mul_le_mul_left e (by omega)
  have hexp1 : (49 * LParam M + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
        routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) =
      (49 * LParam M + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) +
      (49 * LParam M + 1) * (routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1)) +
      (49 * LParam M + 1) * (4 * e) := by ring
  have hexp2 : e * modelPerEdge cfg M r routeC =
      e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) +
      e * (routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3) +
      e * (232 * LParam M) := by unfold modelPerEdge; ring
  rw [hexp1, hexp2]
  omega

/-- Single-node space bound: port graph + outer game + cut/witness scratch (excluding `rfWorkBound`)
fits inside `e * recPerEdgeSpace - 3` whenever `1 ≤ e ≤ M`, `k ≤ 2 * e`, and `lc ≤ e * modelPerEdge`. -/
lemma recNode_space_le {cfg : ParamConfig} {C_sp M r routeC k e lc : ℕ}
    (he1 : 1 ≤ e) (heM : e ≤ M) (hk : k ≤ 2 * e) (hlc : lc ≤ e * modelPerEdge cfg M r routeC) :
    (2 * e + (2 + 20 * e) + portGraphWorkSpace k e + portGraphHeapSpace e + 4 +
      outerGameSpace C_sp M r e lc + (6 * k + 6 * e + 20)) + 3 ≤
      e * recPerEdgeSpace cfg C_sp M r routeC := by
  have h1 : C_sp * coreSpaceBase M r * (lc + (49 * LParam M + 1)) ≤
      e * (C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * LParam M + 1))) := by
    have hsum : lc + (49 * LParam M + 1) ≤ e * (modelPerEdge cfg M r routeC + (49 * LParam M + 1)) := by
      have ha : 49 * LParam M + 1 ≤ e * (49 * LParam M + 1) := Nat.le_mul_of_pos_left _ he1
      have hd : e * (modelPerEdge cfg M r routeC + (49 * LParam M + 1)) =
          e * modelPerEdge cfg M r routeC + e * (49 * LParam M + 1) := by ring
      omega
    calc C_sp * coreSpaceBase M r * (lc + (49 * LParam M + 1))
        ≤ C_sp * coreSpaceBase M r * (e * (modelPerEdge cfg M r routeC + (49 * LParam M + 1))) :=
          Nat.mul_le_mul_left _ hsum
      _ = e * (C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * LParam M + 1))) := by ring
  have hpow5 : (2 * e + 3) ^ 5 ≤ (2 * M + 3) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hloop_sp : (49 * LParam M + 1) * (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) ≤
      e * ((49 * LParam M + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10)) := by
    have hinner : 2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e ≤
        e * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10) := by
      have ha : 2 * C_sp * ((2 * e + 3) ^ 5 + 1) ≤ e * (2 * C_sp * ((2 * M + 3) ^ 5 + 1)) := by
        calc 2 * C_sp * ((2 * e + 3) ^ 5 + 1)
            ≤ 1 * (2 * C_sp * ((2 * M + 3) ^ 5 + 1)) := by
              rw [one_mul]; exact Nat.mul_le_mul_left _ (by omega)
          _ ≤ e * (2 * C_sp * ((2 * M + 3) ^ 5 + 1)) := Nat.mul_le_mul_right _ he1
      have hb : e * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10) =
          e * (2 * C_sp * ((2 * M + 3) ^ 5 + 1)) + 10 * e := by ring
      omega
    calc (49 * LParam M + 1) * (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e)
        ≤ (49 * LParam M + 1) * (e * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10)) :=
          Nat.mul_le_mul_left _ hinner
      _ = e * ((49 * LParam M + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10)) := by ring
  have hpg_sp : portGraphHeapSpace e ≤ e * (41600 * (M + 1) ^ 4) := by
    unfold portGraphHeapSpace
    have he4 : e ^ 4 + 1 ≤ (M + 1) ^ 4 := by
      have h0 : e ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left heM 4
      have h1' : M ^ 4 + 1 ≤ (M + 1) ^ 4 := by
        have : (M + 1) ^ 4 = M ^ 4 + 4 * M ^ 3 + 6 * M ^ 2 + 4 * M + 1 := by ring
        omega
      omega
    have h4 : 41600 * e ^ 4 + 4 ≤ 41600 * (M + 1) ^ 4 := by omega
    calc 41600 * e ^ 4 + 4 ≤ 1 * (41600 * (M + 1) ^ 4) := by omega
      _ ≤ e * (41600 * (M + 1) ^ 4) := Nat.mul_le_mul_right _ he1
  have hbuf : 4 * (49 * LParam M + 1) * e ≤ e * (300 * LParam M) + 4 * e := by
    have : 4 * (49 * LParam M + 1) * e = e * (196 * LParam M) + 4 * e := by ring
    have : 196 * LParam M ≤ 300 * LParam M := by omega
    have := Nat.mul_le_mul_left e this
    omega
  have hlin : (2 * e + (2 + 20 * e) + portGraphWorkSpace k e + 4 + (11 + 12 * e) + 4 * e +
      (6 * k + 6 * e + 20)) + 3 ≤ e * 300 := by
    unfold portGraphWorkSpace; omega
  unfold outerGameSpace outerGameBufSpace outerGameLoopSpace recPerEdgeSpace
  have hdist : e * (C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * LParam M + 1)) +
      (49 * LParam M + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10) +
      41600 * (M + 1) ^ 4 + 300 * LParam M + 300) =
      e * (C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * LParam M + 1))) +
      e * ((49 * LParam M + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10)) +
      e * (41600 * (M + 1) ^ 4) + e * (300 * LParam M) + e * 300 := by ring
  omega

/-- Arithmetic headroom for `RemoveFakeWordBound` (`PruneWordBound` right-hand side) fits inside
`e * recPerWitSpace cfg M r` whenever `1 ≤ e`, `k ≤ 2 * e`, `mF ≤ e`, `1 ≤ Λ`. -/
lemma rfArith_le_witSpace {cfg : ParamConfig} {M r k e mF : ℕ}
    (he1 : 1 ≤ e) (heM : e ≤ M) (hk : k ≤ 2 * e) (hmF : mF ≤ e)
    (h2ML : 2 * M < 2 ^ LParam M) :
    let Λ := Lambda cfg M r
    let nJ := k + mF
    let mJ := e + 2 * mF
    8 * rfCcap 1 Λ * mJ + 4 * rfCcap 1 Λ + 2 * nJ + 2 * mJ + rfHParam e mF 1 Λ + 16 ≤
      e * recPerWitSpace cfg M r ∧
    rfWorkBound k e mF Λ (LParam M) ≤ e * recPerWitSpace cfg M r := by
  intro Λ nJ mJ
  have hΛ : 1 ≤ Λ := one_le_Lambda cfg M r
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hC : rfCcap 1 Λ ≤ 14 * Λ := by unfold rfCcap; simp only [Nat.div_one]; omega
  have h2m_lt : 2 * (e + 2 * mF) + 1 < 2 ^ (LParam M + 2) := by
    have hpow : 2 ^ (LParam M + 2) = 4 * 2 ^ LParam M := by ring
    rw [hpow]; omega
  have hlog1 : Nat.log 2 (2 * (e + 2 * mF) + 1) + 1 ≤ 2 * LParam M := by
    have := Nat.log_lt_of_lt_pow (by omega) h2m_lt; omega
  have hH : rfHParam e mF 1 Λ ≤ 112 * Λ * LParam M + 2 := by
    have h1 : 4 * rfCcap 1 Λ ≤ 56 * Λ := by omega
    unfold rfHParam
    have h2 : 4 * rfCcap 1 Λ * (Nat.log 2 (2 * (e + 2 * mF) + 1) + 1) ≤ (56 * Λ) * (2 * LParam M) :=
      Nat.mul_le_mul h1 hlog1
    have h3 : (56 * Λ) * (2 * LParam M) = 112 * Λ * LParam M := by ring
    rw [h3] at h2; omega
  have hmJ : mJ ≤ 3 * e := by omega
  have hnJ : nJ ≤ 3 * e := by omega
  have h8Cm : 8 * rfCcap 1 Λ * mJ ≤ 336 * Λ * e := by
    calc 8 * rfCcap 1 Λ * mJ ≤ (8 * (14 * Λ)) * (3 * e) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 8 hC) hmJ
      _ = 336 * Λ * e := by ring
  have h336 : 336 * Λ * e ≤ 84 * Λ * LParam M * e := by
    calc 336 * Λ * e = 84 * Λ * 4 * e := by ring
      _ ≤ 84 * Λ * LParam M * e := Nat.mul_le_mul_right e (Nat.mul_le_mul_left (84 * Λ) hL4)
  have h4C : 4 * rfCcap 1 Λ ≤ 14 * Λ * LParam M * e := by
    calc 4 * rfCcap 1 Λ ≤ 56 * Λ := by omega
      _ = 14 * Λ * 4 * 1 := by ring
      _ ≤ 14 * Λ * LParam M * e := Nat.mul_le_mul (Nat.mul_le_mul_left (14 * Λ) hL4) he1
  have h112 : 112 * Λ * LParam M ≤ 112 * Λ * LParam M * e :=
    Nat.le_mul_of_pos_right _ he1
  have h224 : 224 * Λ * LParam M ≤ 224 * Λ * LParam M * e :=
    Nat.le_mul_of_pos_right _ he1
  have hring : e * recPerWitSpace cfg M r = 400 * Λ * LParam M * e + 400 * e := by
    unfold recPerWitSpace; ring
  have hsumL : 84 * Λ * LParam M * e + 14 * Λ * LParam M * e + 112 * Λ * LParam M * e ≤
      400 * Λ * LParam M * e := by
    have : 84 * Λ * LParam M * e + 14 * Λ * LParam M * e + 112 * Λ * LParam M * e =
        210 * (Λ * LParam M * e) := by ring
    have : 400 * Λ * LParam M * e = 400 * (Λ * LParam M * e) := by ring
    omega
  have h224_le : 224 * Λ * LParam M * e ≤ 400 * Λ * LParam M * e := by
    have : 224 * Λ * LParam M * e = 224 * (Λ * LParam M * e) := by ring
    have : 400 * Λ * LParam M * e = 400 * (Λ * LParam M * e) := by ring
    omega
  constructor
  · rw [hring]; omega
  · unfold rfWorkBound; rw [hring]; omega

/-! ## 5. Branch 1: Base Case (`e ≤ QOut`) -/

/-- Execution of `recBaseStmt idx` when `H.edges.length ≤ QOut cfg M r`. -/
lemma recBase_runs {cfg : ParamConfig} {M r w C_core C_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv cfg M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hSub : RecSubprocs M r w pProg idx C_core C_rt C_sp routeC)
    {H : CompactSubgraph} {vertsAddr edgesAddr h nl₀ : ℕ} {st : State} (ω : ℕ → Bool)
    (hRep : H.Represents G H.vertSet) (hXV : H.vertSet ⊆ G.verts)
    (hk_le_2e : H.verts.length ≤ 2 * H.edges.length)
    (hQ : H.edges.length ≤ QOut cfg M r)
    (hV : ListAt st.mem vertsAddr H.verts) (hE : EdgesAt st.mem edgesAddr H.edges)
    (hloc0 : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hnl : st.mem nextLblAddr = nl₀) (hnl_bd : nl₀ + H.verts.length ≤ G.n)
    (hZero : ZeroFrom st.mem h) (hhRoot : hRoot ≤ h)
    (hVA_h : vertsAddr + H.verts.length ≤ h) (hEA_h : edgesAddr + 2 * H.edges.length ≤ h)
    (hdLV : DisjointRange locAddr G.n vertsAddr H.verts.length)
    (hdLE : DisjointRange locAddr G.n edgesAddr (2 * H.edges.length))
    (hdLbV : DisjointRange labelsAddr G.n vertsAddr H.verts.length)
    (hdLbE : DisjointRange labelsAddr G.n edgesAddr (2 * H.edges.length))
    (hdNV : DisjointRange nextLblAddr 1 vertsAddr H.verts.length)
    (hdNE : DisjointRange nextLblAddr 1 edgesAddr (2 * H.edges.length))
    (hSpace : h + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
      (recPerWitSpace cfg M r) H.edges.length < 2 ^ w)
    (hr0 : st.regs 0 = H.verts.length) (hr1 : st.regs 1 = vertsAddr)
    (hr2 : st.regs 2 = H.edges.length) (hr3 : st.regs 3 = edgesAddr)
    (hr5 : st.regs 5 = locAddr) (hr6 : st.regs 6 = labelsAddr)
    (hr7 : st.regs 7 = nextLblAddr) (hr8 : st.regs 8 = h) :
    ∃ h' st' c,
      Runs w pProg ω (recBaseStmt idx) st (.returned h') st' c ∧
      RecNodePost cfg M r C_core C_rt C_sp routeC G locAddr labelsAddr nextLblAddr
        h H st.mem nl₀ h' st'.mem (c + 12) := by
  set k := H.verts.length
  set e := H.edges.length
  have hsubV : ∀ u ∈ H.verts, u < G.n := fun u hu =>
    Finset.mem_range.mp (hXV (List.mem_toFinset.mpr hu))
  have hsubE : ∀ ed ∈ H.edges, ed.1 < G.n ∧ ed.2 < G.n := fun ed hed =>
    env.hv ed (by rw [hRep.2.2] at hed; exact (mem_inside_iff.mp hed).1)
  have hw16 : 16 < 2 ^ w := by have := env.hw250; omega
  have h4k6e_le : 4 * k + 6 * e + 3 ≤
      recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
        (recPerWitSpace cfg M r) e := by
    unfold recTreeSpace
    by_cases he0 : e = 0
    · have hk0 : k = 0 := by omega
      simp [he0, hk0]
    · have hd1 : 1 ≤ recDepthBound (DOut cfg M r) e := by
        cases heq : e with
        | zero => omega
        | succ b => rw [recDepthBound]; simp [one_le_DOut cfg M r]
      have hpe : 14 ≤ recPerEdgeSpace cfg C_sp M r routeC := by unfold recPerEdgeSpace; omega
      have hmul : 14 * e ≤ recDepthBound (DOut cfg M r) e * e * recPerEdgeSpace cfg C_sp M r routeC := by
        calc 14 * e = 1 * e * 14 := by ring
          _ ≤ recDepthBound (DOut cfg M r) e * e * recPerEdgeSpace cfg C_sp M r routeC :=
              Nat.mul_le_mul (Nat.mul_le_mul_right e hd1) hpe
      omega
  have hSpace_k : h + 4 * k + 6 * e + 3 < 2 ^ w := by omega
  let st1 : State := { st with regs := Function.update (Function.update st.regs 10 h) 11 (h + k) }
  have h1 : Runs w pProg ω
      (.assign 10 (.reg 8) ;; .assign 11 (.bin .add (.reg 8) (.reg 0))) st .normal st1 7 := by
    let st0a : State := { st with regs := Function.update st.regs 10 h }
    have ha : Runs w pProg ω (.assign 10 (.reg 8)) st .normal st0a 2 :=
      runs_assign_iff.mpr ⟨h, by simp [Expr.eval, hr8], rfl, rfl, by simp [Expr.size]⟩
    have hb : Runs w pProg ω (.assign 11 (.bin .add (.reg 8) (.reg 0))) st0a .normal st1 4 :=
      runs_assign_iff.mpr ⟨h + k, by simp [Expr.eval, BinOp.eval, st0a, hr8, hr0, (by omega : h + k < 2 ^ w)],
        rfl, rfl, by simp [Expr.size]⟩
    exact runs_seq_iff.mpr (Or.inr ⟨st0a, 2, 4, ha, hb, rfl⟩)
  -- Call bComp
  have hCompCall := runs_call_of_meetsContract (r := 12) (p := pProg) (w := w) (st := st1)
    (args := [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 10, .reg 11])
    (vs := [k, vertsAddr, e, edgesAddr, locAddr, h, h + k]) hSub.hComp
    (by simp [evalArgs, Expr.eval, st1, hr0, hr1, hr2, hr3, hr5])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        have := env.hlocH; have := env.hwN
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨G.n, k, vertsAddr, e, edgesAddr, locAddr, h, h + k, H.verts, H.edges, rfl,
      rfl, hRep.1, hsubV, rfl, hsubE, hV, hE, hloc0,
      ⟨by omega, by omega, by have := env.hlocH; omega, by omega,
       by unfold compLabelsInWorkSpace; omega, by have := env.hwN; omega, hw16⟩,
      ⟨hdLV, hdLE, Or.inl (by have := env.hlocH; omega), Or.inr (by omega),
       Or.inr (by omega), Or.inr (by omega)⟩⟩ ω
  rcases hCompCall with ⟨st2, c2, v2, hrun2, hpost2, h2_12, h2_other, hc2⟩
  dsimp only [compLabelsInContract, st1, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hpost2 hc2
  rw [readList_eq_of_listAt hV, readEdges_eq_of_edgesAt hE] at hpost2
  rcases hpost2 with ⟨_, h2_lblLt, h2_parts, _, h2_pres⟩
  have h2_r : ∀ r' ≤ 11, st2.regs r' = st1.regs r' := fun r' hr' => h2_other r' (by omega)
  have h2_belowH : ∀ a < h, st2.mem a = st.mem a := fun a ha =>
    h2_pres a (Or.inl ha) (Or.inl (by omega))
  have h2_V : ListAt st2.mem vertsAddr H.verts := fun i hi => by
    rw [h2_belowH _ (by omega)]; exact hV i hi
  have h2_nl : st2.mem nextLblAddr = nl₀ := by
    rw [h2_belowH _ (by have := env.hnextH; omega)]; exact hnl
  -- Run writeCompLabelsStmt
  have hWCL := writeCompLabels_triple (w := w) (n := G.n) (k := k) (vertsAddr := vertsAddr)
    (labelsAddr := labelsAddr) (nextLblAddr := nextLblAddr) (tmpLblAddr := h) (nl := nl₀)
    pProg st2 H.verts (by rw [h2_r 0 (by decide)]; simp [st1, hr0])
    (by rw [h2_r 1 (by decide)]; simp [st1, hr1])
    (by rw [h2_r 6 (by decide)]; simp [st1, hr6])
    (by rw [h2_r 7 (by decide)]; simp [st1, hr7])
    (by rw [h2_r 10 (by decide)]; simp [st1])
    rfl hRep.1 hsubV h2_V h2_nl h2_lblLt hdLbV
    (Or.inl (by have := env.hlblH; omega)) env.hdLbN
    (by omega) (by omega) (by have := env.hlblH; omega)
    (by have := env.hwN; omega) (by have := env.hwN; omega) hw16 st2 ω rfl
  rcases hWCL with ⟨o3, st3, c3, hrun3, hq3, hc3⟩
  cases o3 with
  | returned _ => exact False.elim hq3
  | normal =>
    rcases hq3 with ⟨h3_nl, h3_lbl, h3_fr, h3_r⟩
    have h3_0 : st3.regs 0 = k := by rw [h3_r 0 (by decide), h2_r 0 (by decide)]; simp [st1, hr0]
    have h3_2 : st3.regs 2 = e := by rw [h3_r 2 (by decide), h2_r 2 (by decide)]; simp [st1, hr2]
    have h3_8 : st3.regs 8 = h := by rw [h3_r 8 (by decide), h2_r 8 (by decide)]; simp [st1, hr8]
    -- Compute h' = h + 4 * k + 6 * e + 3 and return
    let st3a : State := { st3 with regs := Function.update st3.regs 12 (h + 4 * k) }
    let st3b : State := { st3a with regs := Function.update st3a.regs 12 (h + 4 * k + 6 * e) }
    have h4a : Runs w pProg ω (.assign 12 (.bin .add (.reg 8) (.bin .mul (.const 4) (.reg 0)))) st3 .normal st3a 6 :=
      runs_assign_iff.mpr ⟨h + 4 * k,
        by simp [Expr.eval, BinOp.eval, h3_8, h3_0, (by omega : 4 < 2 ^ w),
             (by omega : 4 * k < 2 ^ w), (by omega : h + 4 * k < 2 ^ w)],
        rfl, rfl, by simp [Expr.size]⟩
    have h4b : Runs w pProg ω (.assign 12 (.bin .add (.reg 12) (.bin .mul (.const 6) (.reg 2)))) st3a .normal st3b 6 :=
      runs_assign_iff.mpr ⟨h + 4 * k + 6 * e,
        by simp [Expr.eval, BinOp.eval, st3a, h3_2, (by omega : 6 < 2 ^ w),
             (by omega : 6 * e < 2 ^ w), (by omega : h + 4 * k + 6 * e < 2 ^ w)],
        rfl, rfl, by simp [Expr.size]⟩
    have h4c : Runs w pProg ω (.ret (.bin .add (.reg 12) (.const 3))) st3b
        (.returned (h + 4 * k + 6 * e + 3)) st3b 4 :=
      runs_ret_iff.mpr ⟨h + 4 * k + 6 * e + 3,
        by simp [Expr.eval, BinOp.eval, st3b, (by omega : 3 < 2 ^ w), hSpace_k],
        rfl, rfl, by simp [Expr.size]⟩
    have hrunAll : Runs w pProg ω (recBaseStmt idx) st (.returned (h + 4 * k + 6 * e + 3)) st3b
        (7 + (c2 + (c3 + (6 + (6 + 4 + 1) + 1) + 1) + 1) + 1) := by
      rcases runs_seq_iff.mp h1 with ⟨_, _, _, hno, _⟩ | ⟨st0a, c0a, c0b, h0a, h0b, hceq⟩
      · cases hno
      have htot := runs_seq_iff.mpr (Or.inr ⟨st0a, c0a, _, h0a,
        runs_seq_iff.mpr (Or.inr ⟨st1, c0b, _, h0b,
          runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
            runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hrun3,
              runs_seq_iff.mpr (Or.inr ⟨st3a, 6, _, h4a,
                runs_seq_iff.mpr (Or.inr ⟨st3b, 6, 4, h4b, h4c, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have : c0a + (c0b + (c2 + (c3 + (6 + (6 + 4 + 1) + 1) + 1) + 1) + 1) + 1 =
          7 + (c2 + (c3 + (6 + (6 + 4 + 1) + 1) + 1) + 1) + 1 := by omega
      rwa [this] at htot
    refine ⟨h + 4 * k + 6 * e + 3, st3b, _, hrunAll,
      { parts := H.componentsOf
        depth := if e = 0 then 0 else 1
        edgeSum := e
        witnessEdgeSum := 0 },
      progRecSpec_base hRep hQ, ?_, by dsimp only [st3b, st3a]; rw [h3_nl],
      by omega,
      by change h + 4 * k + 6 * e + 3 ≤
           h + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
             (recPerWitSpace cfg M r) e
         omega,
      ?_, ?_, ?_, ?_⟩
    · dsimp only [st3b, st3a]
      rw [h3_nl]
      exact labelsMatchParts_componentsOf (localLbl := readList st2.mem h k) hRep
        (by simp [readList, k]) h2_parts (fun i hi => by simp [readList]; exact h3_lbl i hi)
        (fun i hi => by simp [readList]; exact h2_lblLt i hi)
    · intro a ha
      have haN : a ≠ nextLblAddr := by have := env.hnextH; omega
      have haV : ∀ u ∈ H.verts, a ≠ labelsAddr + u := fun u hu => by
        have := hsubV u hu; have := env.hlblH; omega
      dsimp only [st3b, st3a]
      rw [h3_fr a haV haN, h2_pres a (Or.inr (by omega)) (Or.inr (by unfold compLabelsInWorkSpace; omega))]
      exact hZero a (by omega)
    · intro u hu
      have haN : locAddr + u ≠ nextLblAddr := by rcases env.hdLN with hL | hL <;> omega
      have haV : ∀ v ∈ H.verts, locAddr + u ≠ labelsAddr + v := fun v hv => by
        have := hsubV v hv; rcases env.hdLLb with hL | hL <;> omega
      dsimp only [st3b, st3a]
      rw [h3_fr _ haV haN, h2_belowH _ (by have := env.hlocH; omega)]
      exact hloc0 u hu
    · intro a haH haLb haN
      dsimp only [st3b, st3a]
      rw [h3_fr a (fun u hu => haLb u (List.mem_toFinset.mpr hu)) haN, h2_belowH a haH]
    · dsimp only
      dsimp at hc3; simp [argsSize, Expr.size, compLabelsInCost] at hc2
      change k ≤ 2 * e at hk_le_2e
      have hpe : 2500 ≤ recPerEdgeCost cfg C_core C_rt M r routeC := by
        unfold recPerEdgeCost; omega
      have hmul : 2500 * e ≤ e * recPerEdgeCost cfg C_core C_rt M r routeC := by
        calc 2500 * e = e * 2500 := by ring
          _ ≤ e * recPerEdgeCost cfg C_core C_rt M r routeC := Nat.mul_le_mul_left e hpe
      omega

/-! ## 6. Recursive Prefix (`recPortGameStmt`: Port Graph + Outer Game) -/

/-- Execution of `recPortGameStmt idx` when `QOut ParamConfig.default M r < H.edges.length`.
Returns `st3` holding `ownerAddr` (`r10`), `pgAddr` (`r11`), `outResAddr` (`r14`), `h3` (`r15`),
and `tag` (`r16`), together with some `res` satisfying `OuterGameOutAt` and
`OuterGameOutcomeSpec ParamConfig.default M r e (portGraph cloud G H.vertSet) res`. -/
lemma recPortGame_runs {M r w C_core C_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv ParamConfig.default M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hSub : RecSubprocs M r w pProg idx C_core C_rt C_sp routeC)
    {H : CompactSubgraph} {vertsAddr edgesAddr h : ℕ} {st : State} (ω : ℕ → Bool)
    (hRep : H.Represents G H.vertSet) (hSorted : H.verts.Pairwise (· < ·))
    (hXV : H.vertSet ⊆ G.verts) (heM : H.edges.length ≤ M)
    (hk_le_2e : H.verts.length ≤ 2 * H.edges.length)
    (hQlt : QOut ParamConfig.default M r < H.edges.length)
    (hPB : OuterParamBlockAt st.mem paramAddr ParamConfig.default G.n M r)
    (hV : ListAt st.mem vertsAddr H.verts) (hE : EdgesAt st.mem edgesAddr H.edges)
    (hloc0 : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hZero : ZeroFrom st.mem h) (hhRoot : hRoot ≤ h)
    (hVA_h : vertsAddr + H.verts.length ≤ h) (hEA_h : edgesAddr + 2 * H.edges.length ≤ h)
    (hdLV : DisjointRange locAddr G.n vertsAddr H.verts.length)
    (hdLE : DisjointRange locAddr G.n edgesAddr (2 * H.edges.length))
    (hSpace : h + recTreeSpace (DOut ParamConfig.default M r)
      (recPerEdgeSpace ParamConfig.default C_sp M r routeC)
      (recPerWitSpace ParamConfig.default M r) H.edges.length < 2 ^ w)
    (hr0 : st.regs 0 = H.verts.length) (hr1 : st.regs 1 = vertsAddr)
    (hr2 : st.regs 2 = H.edges.length) (hr3 : st.regs 3 = edgesAddr)
    (hr4 : st.regs 4 = paramAddr) (hr5 : st.regs 5 = locAddr) (hr8 : st.regs 8 = h) :
    let e := H.edges.length
    let lc := outerGameMaxCost ParamConfig.default M r routeC e
    let hPG_bound := h + 2 * e + (2 + 20 * e) + portGraphWorkSpace H.verts.length e +
      portGraphHeapSpace e + 4 + outerGameSpace C_sp M r e lc
    ∃ st3 h3 c3 res,
      Runs w pProg ω (recPortGameStmt idx) st .normal st3 c3 ∧
      st3.regs 10 = h ∧
      st3.regs 11 = h + 2 * e ∧
      st3.regs 15 = h3 ∧
      st3.regs 14 + 4 ≤ h3 ∧
      h + 2 * e ≤ h3 ∧
      h3 ≤ hPG_bound ∧
      ZeroFrom st3.mem h3 ∧
      ListAt st3.mem h (portOwnersList H.edges) ∧
      OuterGameOutAt st3.mem (st3.regs 14) h h3 e res ∧
      OuterGameOutcomeSpec ParamConfig.default M r e (portGraph cloud G H.vertSet) res ∧
      st3.regs 16 = st3.mem (st3.regs 14) ∧
      (∀ r' ≤ 9, st3.regs r' = st.regs r') ∧
      (∀ a < h, st3.mem a = st.mem a) ∧
      c3 ≤ outerGameStepBound C_core C_rt r e lc + portGraphCost H.verts.length e + 70 := by
  intro e lc hPG_bound
  set k := H.verts.length
  change st.regs 0 = k at hr0
  change st.regs 2 = e at hr2
  have he_eq : (G.inside H.vertSet).length = e := congrArg List.length hRep.2.2.symm
  have he1 : 1 ≤ e := by unfold QOut at hQlt; omega
  have h2e_pow : 2 * (G.inside H.vertSet).length ≤ (NOf M r) ^ r := by have := env.h2M_pow; omega
  have h2e_L : 2 * (G.inside H.vertSet).length < 2 ^ LParam M := by have := env.h2M_L; omega
  have hlc_le : lc ≤ e * modelPerEdge ParamConfig.default M r routeC :=
    outerGameMaxCost_le_modelPerEdge he1
  have hnode_sp := recNode_space_le (cfg := ParamConfig.default) (C_sp := C_sp) he1 heM hk_le_2e hlc_le
  have hd1 : 1 ≤ recDepthBound (DOut ParamConfig.default M r) e := by
    cases heq : e with
    | zero => omega
    | succ b => rw [recDepthBound]; simp [one_le_DOut ParamConfig.default M r]
  have hTree_ge : e * recPerEdgeSpace ParamConfig.default C_sp M r routeC ≤
      recTreeSpace (DOut ParamConfig.default M r) (recPerEdgeSpace ParamConfig.default C_sp M r routeC)
        (recPerWitSpace ParamConfig.default M r) e := by
    unfold recTreeSpace
    have hmul : 1 * e * recPerEdgeSpace ParamConfig.default C_sp M r routeC ≤
        recDepthBound (DOut ParamConfig.default M r) e * e *
          recPerEdgeSpace ParamConfig.default C_sp M r routeC :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right e hd1)
    rw [one_mul] at hmul
    omega
  change h + recTreeSpace (DOut ParamConfig.default M r)
      (recPerEdgeSpace ParamConfig.default C_sp M r routeC)
      (recPerWitSpace ParamConfig.default M r) e < 2 ^ w at hSpace
  have hPG_w : hPG_bound < 2 ^ w := by dsimp only [hPG_bound, k] at hnode_sp ⊢; omega
  have hw16 : 16 < 2 ^ w := by have := env.hw250; omega
  have hsubV : ∀ u ∈ H.verts, u < G.n := fun u hu =>
    Finset.mem_range.mp (hXV (List.mem_toFinset.mpr hu))
  have hE_inV : ∀ ed ∈ H.edges, ed.1 ∈ H.verts ∧ ed.2 ∈ H.verts := fun ed hed => by
    rw [hRep.2.2] at hed
    have h12 := (mem_inside_iff.mp hed).2
    exact ⟨List.mem_toFinset.mp h12.1, List.mem_toFinset.mp h12.2⟩
  -- Step 1: compute buffer addresses r10..r13
  set pgAddr := h + 2 * e
  set wa := pgAddr + 2 + 20 * e
  set h1 := wa + portGraphWorkSpace k e
  have h1_eq : h1 = wa + 2 * k + 20 * e + 4 := by unfold h1 portGraphWorkSpace; omega
  have hSetup : Triple w pProg (fun s => s = st)
      (.assign 10 (.reg 8) ;;
       .assign 11 (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 2))) ;;
       .assign 12 (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 20) (.reg 2))) ;;
       .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 0))) ;;
       .assign 13 (.bin .add (.reg 13) (.bin .mul (.const 20) (.reg 2))) ;;
       .assign 13 (.bin .add (.reg 13) (.const 4)))
      (normalPost fun s' =>
        s'.mem = st.mem ∧ s'.regs 10 = h ∧ s'.regs 11 = pgAddr ∧
        s'.regs 12 = wa ∧ s'.regs 13 = h1 ∧ (∀ r' ≤ 9, s'.regs r' = st.regs r'))
      (fun _ => 38) := by
    intro s ω hs; subst s
    have hpg_lt : pgAddr < 2 ^ w := by dsimp only [hPG_bound, pgAddr] at hPG_w ⊢; omega
    have hwa_lt : wa < 2 ^ w := by dsimp only [hPG_bound, wa, pgAddr] at hPG_w ⊢; omega
    have hh1_lt : h1 < 2 ^ w := by dsimp only [hPG_bound, h1, wa, pgAddr, k] at hPG_w ⊢; omega
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := h) (by simp [Expr.eval, hr8]) ?_
    refine runs_seq_assign_le (v := pgAddr)
      (by simp [Expr.eval, BinOp.eval, hr2, (by omega : 2 < 2 ^ w),
            (by omega : 2 * e < 2 ^ w), pgAddr, (by omega : h + 2 * e < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := wa)
      (by simp [Expr.eval, BinOp.eval, hr2, (by omega : 2 < 2 ^ w), (by omega : 20 < 2 ^ w),
            (by omega : pgAddr + 2 < 2 ^ w), (by omega : 20 * e < 2 ^ w), wa,
            (by omega : pgAddr + 2 + 20 * e < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := wa + 2 * k)
      (by simp [Expr.eval, BinOp.eval, hr0, (by omega : 2 < 2 ^ w),
            (by omega : 2 * k < 2 ^ w), (by omega : wa + 2 * k < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := wa + 2 * k + 20 * e)
      (by simp [Expr.eval, BinOp.eval, hr2, (by omega : 20 < 2 ^ w),
            (by omega : 20 * e < 2 ^ w), (by omega : wa + 2 * k + 20 * e < 2 ^ w)]) ?_
    refine runs_assign_le (v := h1)
      (by simp [Expr.eval, BinOp.eval, (by omega : 4 < 2 ^ w), h1_eq,
            (by omega : wa + 2 * k + 20 * e + 4 < 2 ^ w)])
      ⟨rfl, by simp, by simp, by simp, by simp, fun r' hr' => by
        dsimp only
        rw [Function.update_of_ne (by omega : r' ≠ 13), Function.update_of_ne (by omega : r' ≠ 13),
            Function.update_of_ne (by omega : r' ≠ 13), Function.update_of_ne (by omega : r' ≠ 12),
            Function.update_of_ne (by omega : r' ≠ 11), Function.update_of_ne (by omega : r' ≠ 10)]⟩
      (by simp [Expr.size])
  rcases hSetup st ω rfl with ⟨o1, st1, c1, hrun1, hq1, hc1⟩
  cases o1 with
  | returned _ => exact False.elim hq1
  | normal =>
    rcases hq1 with ⟨h1_mem, h1_10, h1_11, h1_12, h1_13, h1_r⟩
    have hPortCall := runs_call_of_meetsContract (r := 13) (p := pProg) (w := w) (st := st1)
      (args := [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 10, .reg 11, .reg 12, .reg 13])
      (vs := [k, vertsAddr, e, edgesAddr, locAddr, h, pgAddr, wa, h1]) hSub.hPort
      (by simp [evalArgs, Expr.eval, h1_r 0 (by decide), hr0, h1_r 1 (by decide), hr1,
            h1_r 2 (by decide), hr2, h1_r 3 (by decide), hr3, h1_r 5 (by decide), hr5,
            h1_10, h1_11, h1_12, h1_13])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          have := env.hlocH; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨G.n, k, vertsAddr, e, edgesAddr, locAddr, h, pgAddr, wa, h1, H.verts, H.edges, rfl,
        rfl, hSorted, hsubV, rfl, hE_inV, h1_mem ▸ hV, h1_mem ▸ hE, h1_mem ▸ hloc0,
        fun a ha => h1_mem ▸ hZero a (by omega),
        ⟨by omega, by omega, by have := env.hlocH; omega, by omega, by omega, by omega,
         by omega, hw16⟩,
        ⟨hdLV, hdLE, Or.inl (by have := env.hlocH; omega), Or.inl (by have := env.hlocH; omega),
         Or.inl (by have := env.hlocH; omega), Or.inr (by omega), Or.inr (by omega),
         Or.inl (by omega), Or.inl (by omega), Or.inr (by omega), Or.inr (by omega),
         Or.inl (by omega), Or.inr (by omega), Or.inr (by omega)⟩⟩ ω
    rcases hPortCall with ⟨st2, c2, h2, hrun2, hpost2, h2_13, h2_other, hc2⟩
    dsimp only [portGraphContract, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hpost2 hc2
    rw [h1_mem, readList_eq_of_listAt hV, readEdges_eq_of_edgesAt hE] at hpost2
    rcases hpost2 with ⟨_, _, hPG_G, hh2_ge, hh2_le, hZero2, hFrame2⟩
    rcases hPG_G G hRep.2.2.symm with ⟨hPg2, hOwn2⟩
    have h2_belowH : ∀ a < h, st2.mem a = st.mem a := fun a ha =>
      hFrame2 a (by omega) (Or.inl ha) (Or.inl (by omega)) (Or.inl (by omega))
    have h2_PB : OuterParamBlockAt st2.mem paramAddr ParamConfig.default G.n M r := by
      have hp : ∀ j < 12, st2.mem (paramAddr + j) = st.mem (paramAddr + j) := fun j hj =>
        h2_belowH _ (by have := env.hparH; omega)
      refine ⟨by rw [hp 0 (by decide)]; exact hPB.1, by rw [hp 1 (by decide)]; exact hPB.2.1,
        by rw [hp 2 (by decide)]; exact hPB.2.2.1, by rw [hp 3 (by decide)]; exact hPB.2.2.2.1,
        by rw [hp 4 (by decide)]; exact hPB.2.2.2.2.1, by rw [hp 5 (by decide)]; exact hPB.2.2.2.2.2.1,
        by rw [hp 6 (by decide)]; exact hPB.2.2.2.2.2.2.1, by rw [hp 7 (by decide)]; exact hPB.2.2.2.2.2.2.2.1,
        by rw [hp 8 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.1, by rw [hp 9 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.1,
        by rw [hp 10 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.1, by rw [hp 11 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.2⟩
    let st2a : State := { st2 with regs := Function.update st2.regs 14 h2 }
    let st2b : State := { st2a with regs := Function.update st2a.regs 15 (h2 + 4) }
    have h2a : Runs w pProg ω (.assign 14 (.reg 13)) st2 .normal st2a 2 :=
      runs_assign_iff.mpr ⟨h2, by simp [Expr.eval, h2_13], rfl, rfl, by simp [Expr.size]⟩
    have h2b : Runs w pProg ω (.assign 15 (.bin .add (.reg 13) (.const 4))) st2a .normal st2b 4 :=
      runs_assign_iff.mpr ⟨h2 + 4,
        by simp [Expr.eval, BinOp.eval, st2a, h2_13, (by omega : 4 < 2 ^ w), (by omega : h2 + 4 < 2 ^ w)],
        rfl, rfl, by simp [Expr.size]⟩
    have h2_r : ∀ r' ≤ 9, st2b.regs r' = st.regs r' := fun r' hr' => by
      dsimp only [st2b, st2a]
      rw [Function.update_of_ne (by omega : r' ≠ 15), Function.update_of_ne (by omega : r' ≠ 14),
          h2_other r' (by omega), h1_r r' hr']
    have h2b_11 : st2b.regs 11 = pgAddr := by
      dsimp only [st2b, st2a]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          h2_other 11 (by decide), h1_11]
    set Hhat := portGraph cloud G H.vertSet
    have hHhat_n : Hhat.n = 2 * e := by rw [portGraph_n, he_eq]
    have hHhat_m : Hhat.m ≤ 10 * e := by rw [← he_eq]; exact portGraph_m_le cloud_isCloudExpander G H.vertSet
    have hGameCall := runs_call_of_meetsContract (r := 15) (p := pProg) (w := w) (st := st2b)
      (args := [.reg 2, .reg 11, .reg 4, .reg 14, .reg 15])
      (vs := [e, pgAddr, paramAddr, h2, h2 + 4]) hSub.hGame
      (by simp only [evalArgs, Expr.eval, h2_r 2 (by decide), hr2, h2b_11, h2_r 4 (by decide), hr4]
          simp [st2b, st2a])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          have := env.hparH; rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨G.n, e, pgAddr, paramAddr, h2, h2 + 4, Hhat, rfl, hPg2, hHhat_n, hHhat_m,
        portGraph_isValid cloud_isCloudExpander G H.vertSet,
        portGraph_isLoopless cloud_isCloudExpander G H.vertSet,
        portGraph_deg_le cloud_isCloudExpander G H.vertSet,
        h2_PB, he1, env.hr1, env.hrl, env.hN2, by omega, by omega,
        one_le_DOut ParamConfig.default M r,
        fun a ha => hZero2 a (by omega), by omega, by have := env.hparH; omega, le_rfl,
        Or.inr (by omega), Or.inr (by have := env.hparH; omega),
        by change h2 + 4 + outerGameSpace C_sp M r e lc < 2 ^ w
           dsimp only [hPG_bound, lc] at hPG_w; omega,
        by have := env.hN2M_w; have : NOf M r * (2 * e) ≤ NOf M r * (2 * M) :=
          Nat.mul_le_mul_left _ (by omega); omega, env.hwb, env.hwM, env.hwR, hw16⟩ ω
    rcases hGameCall with ⟨st3a, c3g, h3, hrun3g, hpost3, h3_15, h3_other, hc3g⟩
    dsimp only [outerGameContract, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hpost3 hc3g
    rw [readGraph_eq_of_graphAt hPg2] at hpost3
    rcases hpost3 with ⟨⟨res, hOut3, hSpec3⟩, hh3_ge, hh3_le, hZero3, hFrame3⟩
    have h3_14 : st3a.regs 14 = h2 := by rw [h3_other 14 (by decide)]; simp [st2b, st2a]
    let st3 : State := { st3a with regs := Function.update st3a.regs 16 (st3a.mem h2) }
    have hLoadTag : Runs w pProg ω (.assign 16 (.load (.reg 14))) st3a .normal st3 3 :=
      runs_assign_iff.mpr ⟨st3a.mem h2, by simp [Expr.eval, h3_14], rfl, rfl, by simp [Expr.size]⟩
    have hrunAll : Runs w pProg ω (recPortGameStmt idx) st .normal st3
        (c1 + (c2 + (2 + (4 + (c3g + 3 + 1) + 1) + 1) + 1) + 1) := by
      rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, hno, _⟩ | ⟨sa, ca, cb, ha, hb, rfl⟩
      · cases hno
      rcases runs_seq_iff.mp hb with ⟨_, _, _, hno, _⟩ | ⟨sb, cb1, cb2, hb1, hb2, rfl⟩
      · cases hno
      rcases runs_seq_iff.mp hb2 with ⟨_, _, _, hno, _⟩ | ⟨sc, cc1, cc2, hc1', hc2', rfl⟩
      · cases hno
      rcases runs_seq_iff.mp hc2' with ⟨_, _, _, hno, _⟩ | ⟨sd, cd1, cd2, hd1', hd2', rfl⟩
      · cases hno
      rcases runs_seq_iff.mp hd2' with ⟨_, _, _, hno, _⟩ | ⟨se, ce1, ce2, he1', he2', rfl⟩
      · cases hno
      have htot := runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, ha,
        runs_seq_iff.mpr (Or.inr ⟨sb, cb1, _, hb1,
          runs_seq_iff.mpr (Or.inr ⟨sc, cc1, _, hc1',
            runs_seq_iff.mpr (Or.inr ⟨sd, cd1, _, hd1',
              runs_seq_iff.mpr (Or.inr ⟨se, ce1, _, he1',
                runs_seq_iff.mpr (Or.inr ⟨st1, ce2, _, he2',
                  runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
                    runs_seq_iff.mpr (Or.inr ⟨st2a, 2, _, h2a,
                      runs_seq_iff.mpr (Or.inr ⟨st2b, 4, _, h2b,
                        runs_seq_iff.mpr (Or.inr ⟨st3a, c3g, 3, hrun3g, hLoadTag, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have heq : ca + (cb1 + (cc1 + (cd1 + (ce1 + (ce2 + (c2 + (2 + (4 + (c3g + 3 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 =
          (ca + (cb1 + (cc1 + (cd1 + (ce1 + ce2 + 1) + 1) + 1) + 1) + 1) +
            (c2 + (2 + (4 + (c3g + 3 + 1) + 1) + 1) + 1) + 1 := by omega
      rwa [heq] at htot
    refine ⟨st3, h3, _, res, hrunAll,
      by simp [st3, h3_other 10 (by decide), st2b, st2a, h2_other 10 (by decide), h1_10],
      by simp [st3, h3_other 11 (by decide), h2b_11],
      by simp [st3, h3_15], by simp [st3, h3_14]; omega, by omega,
      by dsimp only [h1, wa, pgAddr, k, portGraphWorkSpace] at hh2_le
         dsimp only [hPG_bound, lc, portGraphWorkSpace]
         omega, hZero3, ?_, ?_, hSpec3,
      by simp [st3, h3_14], fun r' hr' => by simp [st3, Function.update_of_ne (by omega : r' ≠ 16),
        h3_other r' (by omega), h2_r r' hr'], fun a ha => ?_, ?_⟩
    · rw [hRep.2.2]
      exact listAt_portOwnersList_of_portOwner fun p hp => by
        dsimp only [st3]
        rw [hFrame3 (h + p) (by omega) (Or.inl (by omega))]
        exact hOwn2 p (by omega)
    · simp only [st3]
      rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 16), h3_14]
      exact hOut3.mono_h (by omega)
    · dsimp only [st3]
      rw [hFrame3 a (by omega) (Or.inl (by omega)), h2_belowH a ha]
    · dsimp at hc1
      simp only [argsSize, Expr.size, Nat.add_zero] at hc2 hc3g
      dsimp only [lc]
      omega

end MinCostFlow.ExpanderDecomp
