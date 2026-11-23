module

public import MinCostFlow.ExpanderDecomp.OuterProgRecChild
import MinCostFlow.ExpanderDecomp.OuterProgRecCut
import MinCostFlow.ExpanderDecomp.OuterProgRecWit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recursive Outer Expander Decomposition Specification (`OuterProgRec`)

Proves `outerDecompRecProc_spec` by strong induction on `H.edges.length` together with the global
cost and space bridges (`outerRec_cost_le_totalTimeRaw`, `coreSpaceBase_rOf_le`,
`outerRec_treeSpace_le_outerDecompSpace`), re-exporting `OuterProgRecChild`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 4. Main Strong Induction (`outerDecompRecProc_spec`) -/

/-- Complete Word-RAM specification of `outerDecompRecProc idx` proved by strong induction on
`H.edges.length`: for every active compact subgraph `H` (`H.edges.length ≤ M`) with strictly
increasing vertex list, `outerDecompRecProc` terminates with `RecNodePost`. -/
theorem outerDecompRecProc_spec {M r w C_core C_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv ParamConfig.default M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hSub : RecSubprocs M r w pProg idx C_core C_rt C_sp routeC)
    (ω : ℕ → Bool) :
    ∀ eBound : ℕ,
      RecIH ParamConfig.default M r w C_core C_rt C_sp routeC pProg idx G
        paramAddr locAddr labelsAddr nextLblAddr hRoot ω eBound := by
  let cfg := ParamConfig.default
  intro eBound
  induction eBound with
  | zero =>
    intro H vertsAddr edgesAddr h nl₀ st heB hRep hXV _ hXdeg _ hRoot_le
      hVA_h hEA_h hdLV hdLbV hdNV hdLE hdLbE hdNE hPB hV hE hloc0 hnl hnl_le hZero hSpace
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
    have hQ : H.edges.length ≤ QOut cfg M r := by omega
    have hw250 := env.hw250
    let st1 : State := { st with regs := Function.update st.regs 9 (QOut cfg M r) }
    have h1 : Runs w pProg ω (.assign 9 (.load (.bin .add (.reg 4) (.const 10)))) st .normal st1 5 :=
      runs_assign_iff.mpr ⟨QOut cfg M r,
        by simp [cfg, Expr.eval, BinOp.eval, hr4, (by omega : 10 < 2 ^ w),
              (by have := env.hparH; omega : paramAddr + 10 < 2 ^ w), hPB.2.2.2.2.2.2.2.2.2.2.1],
        rfl, rfl, by simp [Expr.size]⟩
    have hBase := recBase_runs (st := st1) env hSub ω hRep hXV (verts_length_le_two_mul_edges hRep hXdeg)
      hQ hV hE hloc0 hnl hnl_le hZero hRoot_le hVA_h hEA_h hdLV hdLE hdLbV hdLbE hdNV hdNE hSpace
      (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr2]) (by simp [st1, hr3])
      (by simp [st1, hr5]) (by simp [st1, hr6]) (by simp [st1, hr7]) (by simp [st1, hr8])
    rcases hBase with ⟨h', st', cB, hrunB, hPostB⟩
    have hCond : Runs w pProg ω
        (.cond (.bin .lt (.reg 9) (.reg 2))
          (recPortGameStmt idx ;; .cond (.reg 16) (recWitnessStmt idx) (recCutStmt idx))
          (recBaseStmt idx)) st1 (.returned h') st' (3 + cB + 1) :=
      runs_cond_iff.mpr ⟨0, cB, by simp [Expr.eval, BinOp.eval, st1, hr2, Nat.not_lt.mpr hQ],
        by simpa using hrunB, by simp [Expr.size]⟩
    have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, 5, 3 + cB + 1, h1, hCond, rfl⟩)
    rcases hPostB with ⟨o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9⟩
    refine ⟨h', st', _, hrun, o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, by omega⟩
  | succ n ih =>
    intro H vertsAddr edgesAddr h nl₀ st heB hRep hXV hSorted hXdeg heM hRoot_le
      hVA_h hEA_h hdLV hdLbV hdNV hdLE hdLbE hdNE hPB hV hE hloc0 hnl hnl_le hZero hSpace
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
    have hw250 := env.hw250
    have hw_ne0 : w ≠ 0 := by intro h0; subst h0; simp at hw250
    let st1 : State := { st with regs := Function.update st.regs 9 (QOut cfg M r) }
    have h1 : Runs w pProg ω (.assign 9 (.load (.bin .add (.reg 4) (.const 10)))) st .normal st1 5 :=
      runs_assign_iff.mpr ⟨QOut cfg M r,
        by simp [cfg, Expr.eval, BinOp.eval, hr4, (by omega : 10 < 2 ^ w),
              (by have := env.hparH; omega : paramAddr + 10 < 2 ^ w), hPB.2.2.2.2.2.2.2.2.2.2.1],
        rfl, rfl, by simp [Expr.size]⟩
    by_cases hQ : H.edges.length ≤ QOut cfg M r
    · have hBase := recBase_runs (st := st1) env hSub ω hRep hXV (verts_length_le_two_mul_edges hRep hXdeg)
        hQ hV hE hloc0 hnl hnl_le hZero hRoot_le hVA_h hEA_h hdLV hdLE hdLbV hdLbE hdNV hdNE hSpace
        (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr2]) (by simp [st1, hr3])
        (by simp [st1, hr5]) (by simp [st1, hr6]) (by simp [st1, hr7]) (by simp [st1, hr8])
      rcases hBase with ⟨h', st', cB, hrunB, hPostB⟩
      have hCond : Runs w pProg ω
          (.cond (.bin .lt (.reg 9) (.reg 2))
            (recPortGameStmt idx ;; .cond (.reg 16) (recWitnessStmt idx) (recCutStmt idx))
            (recBaseStmt idx)) st1 (.returned h') st' (3 + cB + 1) :=
        runs_cond_iff.mpr ⟨0, cB, by simp [Expr.eval, BinOp.eval, st1, hr2, Nat.not_lt.mpr hQ],
          by simpa using hrunB, by simp [Expr.size]⟩
      have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, 5, 3 + cB + 1, h1, hCond, rfl⟩)
      rcases hPostB with ⟨o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9⟩
      refine ⟨h', st', _, hrun, o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, by omega⟩
    · have hQlt : QOut cfg M r < H.edges.length := by omega
      have hPG := recPortGame_runs (st := st1) env hSub ω hRep hSorted hXV heM
        (verts_length_le_two_mul_edges hRep hXdeg) hQlt
        hPB hV hE hloc0 hZero hRoot_le hVA_h hEA_h hdLV hdLE hSpace
        (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr2]) (by simp [st1, hr3])
        (by simp [st1, hr4]) (by simp [st1, hr5]) (by simp [st1, hr8])
      rcases hPG with ⟨st3, h3, c3, res, hrun3, h3_10, _, h3_15, h3_14_le, h3_ge, h3_le,
        hZero3, hOwn3, hOut3, hSpec3, h3_16, h3_r1, h3_belowH, hc3⟩
      cases res with
      | cut U =>
        have hTag0 : st3.regs 16 = 0 := by rw [h3_16]; exact hOut3.1
        have hCut := recCut_runs (st := st1) env hSub ih heB hRep hXV hSorted hXdeg heM hQlt hSpec3
          hRoot_le hVA_h hEA_h hdLV hdLE hdLbE hdNE hPB hV hE hloc0 hnl hnl_le hSpace
          (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr2]) (by simp [st1, hr3])
          (by simp [st1, hr4]) (by simp [st1, hr5]) (by simp [st1, hr6]) (by simp [st1, hr7])
          h3_10 h3_15 h3_14_le h3_ge h3_le hZero3 hOwn3 hOut3 h3_r1 h3_belowH hc3
        rcases hCut with ⟨h', st', cB, hrunB, hPost⟩
        have hInner : Runs w pProg ω
            (.cond (.reg 16) (recWitnessStmt idx) (recCutStmt idx)) st3 (.returned h') st' (1 + cB + 1) :=
          runs_cond_iff.mpr ⟨0, cB, by simp [Expr.eval, hTag0], by simpa using hrunB, by simp [Expr.size]⟩
        have hSeq2 := runs_seq_iff.mpr (Or.inr ⟨st3, c3, 1 + cB + 1, hrun3, hInner, rfl⟩)
        have hCond : Runs w pProg ω
            (.cond (.bin .lt (.reg 9) (.reg 2))
              (recPortGameStmt idx ;; .cond (.reg 16) (recWitnessStmt idx) (recCutStmt idx))
              (recBaseStmt idx)) st1 (.returned h') st' (3 + (c3 + (1 + cB + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, c3 + (1 + cB + 1) + 1, by simp [Expr.eval, BinOp.eval, st1, hr2, hQlt, hw_ne0],
            by simpa using hSeq2, by simp [Expr.size]⟩
        have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, h1, hCond, rfl⟩)
        rcases hPost with ⟨o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9⟩
        refine ⟨h', st', _, hrun, o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, by omega⟩
      | witness W_out F_out =>
        have hTag1 : st3.regs 16 = 1 := by rw [h3_16]; exact hOut3.1
        have hWit := recWitness_runs (st := st1) env hSub ih heB hRep hXV hSorted hXdeg heM hQlt hSpec3
          hRoot_le hVA_h hEA_h hdLV hdLbV hdNV hdLE hdLbE hdNE hPB hV hE hloc0 hnl hnl_le hSpace
          (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr2]) (by simp [st1, hr3])
          (by simp [st1, hr4]) (by simp [st1, hr5]) (by simp [st1, hr6]) (by simp [st1, hr7])
          h3_10 h3_15 h3_14_le h3_ge h3_le hZero3 hOwn3 hOut3 h3_r1 h3_belowH hc3
        rcases hWit with ⟨h', st', cB, hrunB, hPost⟩
        have hInner : Runs w pProg ω
            (.cond (.reg 16) (recWitnessStmt idx) (recCutStmt idx)) st3 (.returned h') st' (1 + cB + 1) :=
          runs_cond_iff.mpr ⟨1, cB, by simp [Expr.eval, hTag1], by simpa using hrunB, by simp [Expr.size]⟩
        have hSeq2 := runs_seq_iff.mpr (Or.inr ⟨st3, c3, 1 + cB + 1, hrun3, hInner, rfl⟩)
        have hCond : Runs w pProg ω
            (.cond (.bin .lt (.reg 9) (.reg 2))
              (recPortGameStmt idx ;; .cond (.reg 16) (recWitnessStmt idx) (recCutStmt idx))
              (recBaseStmt idx)) st1 (.returned h') st' (3 + (c3 + (1 + cB + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, c3 + (1 + cB + 1) + 1, by simp [Expr.eval, BinOp.eval, st1, hr2, hQlt, hw_ne0],
            by simpa using hSeq2, by simp [Expr.size]⟩
        have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, h1, hCond, rfl⟩)
        rcases hPost with ⟨o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9⟩
        refine ⟨h', st', _, hrun, o, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, by omega⟩

/-! ## 5. Global Cost and Space Bridges to `totalTimeRaw` and `outerDecompSpace` -/

private lemma modelPerEdge_le_sum (cfg : ParamConfig) (M r routeC : ℕ) :
    modelPerEdge cfg M r routeC ≤
      (routeC * 2 ^ 29 + 232) *
        ((tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
          tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3 + LParam M) := by
  set A := (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)
  set B := tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3
  set L := LParam M
  set c29 := (2 ^ 29 : ℕ)
  have hA : 2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) = 2 * A := by
    dsimp only [A]; ring
  have hB : routeC * c29 * tParam M * (bOut cfg M) ^ 3 * L ^ 3 = routeC * c29 * B := by
    dsimp only [B]; ring
  have h1 : 2 * A ≤ (routeC * c29 + 232) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : routeC * c29 * B ≤ (routeC * c29 + 232) * B := Nat.mul_le_mul_right B (by omega)
  have h3 : 232 * L ≤ (routeC * c29 + 232) * L := Nat.mul_le_mul_right L (by omega)
  have hdist : (routeC * c29 + 232) * (A + B + L) =
      (routeC * c29 + 232) * A + (routeC * c29 + 232) * B + (routeC * c29 + 232) * L := by ring
  unfold modelPerEdge
  change 2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
      routeC * c29 * tParam M * (bOut cfg M) ^ 3 * L ^ 3 + 232 * L ≤ (routeC * c29 + 232) * (A + B + L)
  rw [hA, hB, hdist]
  omega

/-- Bridges the recursion step bound `o.edgeSum * recPerEdgeCost + o.witnessEdgeSum * recPerWitCost + 600`
to `outerRecCostK C_core C_rt routeC * totalTimeRaw cfg n M r + 600`. -/
theorem outerRec_cost_le_totalTimeRaw {cfg : ParamConfig} {C_core C_rt routeC n M r eSum wSum : ℕ}
    (hr_le : r ≤ LParam M) (heSum : eSum ≤ HDepth cfg M r * M) (hwSum : 15 * wSum ≤ 16 * M) :
    eSum * recPerEdgeCost cfg C_core C_rt M r routeC + wSum * recPerWitCost cfg M r + 600 ≤
      outerRecCostK C_core C_rt routeC * totalTimeRaw cfg n M r + 600 := by
  set A := (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)
  set B := tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3
  set L := LParam M
  set Λ := Lambda cfg M r
  set rs := runnerScale explicitProgram
  set c29 := (2 ^ 29 : ℕ)
  set c30 := (2 ^ 30 : ℕ)
  set c31 := (2 ^ 31 : ℕ)
  have h2c30 : 2 * c30 = c31 := by decide
  have hL4 : 4 ≤ L := four_le_LParam M
  have hLam1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hCT1 : 1 ≤ cfg.CTotal := by
    unfold ParamConfig.CTotal; have := cfg.hu; have := Nat.pow_pos (show 0 < cfg.u by omega) (n := 3)
    omega
  have hmodel : modelPerEdge cfg M r routeC ≤ (routeC * c29 + 232) * (A + B + L) :=
    modelPerEdge_le_sum cfg M r routeC
  have hpe : recPerEdgeCost cfg C_core C_rt M r routeC ≤
      outerRecCostK C_core C_rt routeC * (A + B + L) := by
    unfold recPerEdgeCost outerRecCostK
    change outerGameCostFactor C_core C_rt * (modelPerEdge cfg M r routeC + 2) +
        (rs * 760 + 8000) + 40 * r ≤
      (outerGameCostFactor C_core C_rt * (routeC * c29 + 234) + rs * 760 + c31 + 20000) * (A + B + L)
    have h1L : 1 ≤ A + B + L := by omega
    have h40r : 40 * r ≤ 40 * (A + B + L) := by omega
    have hconst : rs * 760 + 8000 ≤ (rs * 760 + 8000) * (A + B + L) := Nat.le_mul_of_pos_right _ h1L
    have hfac : outerGameCostFactor C_core C_rt * (modelPerEdge cfg M r routeC + 2) ≤
        outerGameCostFactor C_core C_rt * ((routeC * c29 + 234) * (A + B + L)) := by
      apply Nat.mul_le_mul_left
      have : (routeC * c29 + 234) * (A + B + L) =
          (routeC * c29 + 232) * (A + B + L) + 2 * (A + B + L) := by ring
      omega
    have hsum : (outerGameCostFactor C_core C_rt * (routeC * c29 + 234) + (rs * 760 + 8000) + 40) * (A + B + L) ≤
        (outerGameCostFactor C_core C_rt * (routeC * c29 + 234) + rs * 760 + c31 + 20000) * (A + B + L) :=
      Nat.mul_le_mul_right _ (by linarith)
    have hdist : (outerGameCostFactor C_core C_rt * (routeC * c29 + 234) + (rs * 760 + 8000) + 40) * (A + B + L) =
        outerGameCostFactor C_core C_rt * ((routeC * c29 + 234) * (A + B + L)) +
        (rs * 760 + 8000) * (A + B + L) + 40 * (A + B + L) := by ring
    linarith
  have hpw : 2 * recPerWitCost cfg M r ≤ outerRecCostK C_core C_rt routeC * (Λ ^ 2 * L ^ 2) := by
    unfold recPerWitCost outerRecCostK
    change 2 * (c30 * Λ ^ 2 * L ^ 2 + 2000) ≤
      (outerGameCostFactor C_core C_rt * (routeC * c29 + 234) + rs * 760 + c31 + 20000) * (Λ ^ 2 * L ^ 2)
    have hLL1 : 1 ≤ Λ ^ 2 * L ^ 2 := Nat.mul_pos (Nat.pow_pos hLam1) (Nat.pow_pos (by omega))
    have h4000 : 4000 ≤ 4000 * (Λ ^ 2 * L ^ 2) := Nat.le_mul_of_pos_right _ hLL1
    have h231 : 2 * (c30 * Λ ^ 2 * L ^ 2 + 2000) = c31 * (Λ ^ 2 * L ^ 2) + 4000 := by
      rw [← h2c30]; ring
    have hle : (c31 + 4000) * (Λ ^ 2 * L ^ 2) ≤
        (outerGameCostFactor C_core C_rt * (routeC * c29 + 234) + rs * 760 + c31 + 20000) * (Λ ^ 2 * L ^ 2) :=
      Nat.mul_le_mul_right _ (by
        have h0 := Nat.zero_le (outerGameCostFactor C_core C_rt * (routeC * c29 + 234) + rs * 760)
        linarith)
    have hdist : (c31 + 4000) * (Λ ^ 2 * L ^ 2) = c31 * (Λ ^ 2 * L ^ 2) + 4000 * (Λ ^ 2 * L ^ 2) := by ring
    linarith
  have hw2M : wSum ≤ 2 * M := by omega
  have hTermE : eSum * recPerEdgeCost cfg C_core C_rt M r routeC ≤
      outerRecCostK C_core C_rt routeC * (M * HDepth cfg M r * (A + B + L)) := by
    calc eSum * recPerEdgeCost cfg C_core C_rt M r routeC
        ≤ (HDepth cfg M r * M) * (outerRecCostK C_core C_rt routeC * (A + B + L)) :=
          Nat.mul_le_mul heSum hpe
      _ = outerRecCostK C_core C_rt routeC * (M * HDepth cfg M r * (A + B + L)) := by ring
  have hTermW : wSum * recPerWitCost cfg M r ≤
      outerRecCostK C_core C_rt routeC * (M * Λ ^ 2 * L ^ 2) := by
    calc wSum * recPerWitCost cfg M r
        ≤ (2 * M) * recPerWitCost cfg M r := Nat.mul_le_mul_right _ hw2M
      _ = M * (2 * recPerWitCost cfg M r) := by ring
      _ ≤ M * (outerRecCostK C_core C_rt routeC * (Λ ^ 2 * L ^ 2)) := Nat.mul_le_mul_left M hpw
      _ = outerRecCostK C_core C_rt routeC * (M * Λ ^ 2 * L ^ 2) := by ring
  have hTot_ge : M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2 ≤ totalTimeRaw cfg n M r := by
    unfold totalTimeRaw
    change M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2 ≤
      cfg.CTotal * (n + M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2)
    calc M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2
        ≤ 1 * (n + M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2) := by omega
      _ ≤ cfg.CTotal * (n + M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2) :=
          Nat.mul_le_mul_right _ hCT1
  have hcomb : eSum * recPerEdgeCost cfg C_core C_rt M r routeC + wSum * recPerWitCost cfg M r ≤
      outerRecCostK C_core C_rt routeC * totalTimeRaw cfg n M r := by
    calc eSum * recPerEdgeCost cfg C_core C_rt M r routeC + wSum * recPerWitCost cfg M r
        ≤ outerRecCostK C_core C_rt routeC * (M * HDepth cfg M r * (A + B + L)) +
          outerRecCostK C_core C_rt routeC * (M * Λ ^ 2 * L ^ 2) := Nat.add_le_add hTermE hTermW
      _ = outerRecCostK C_core C_rt routeC * (M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2) := by ring
      _ ≤ outerRecCostK C_core C_rt routeC * totalTimeRaw cfg n M r := Nat.mul_le_mul_left _ hTot_ge
  omega

private lemma two_mul_add_four_pow_five_le (k : ℕ) : (2 * k + 4) ^ 5 ≤ 2 ^ 30 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases hk : k < 5
    · interval_cases k <;> decide
    · have ht : 2 * k + 4 = (2 * k - 10) + 14 := by omega
      have ht1 : 2 * (k + 1) + 4 = (2 * k - 10) + 16 := by omega
      set t := 2 * k - 10
      have hstep : (t + 16) ^ 5 ≤ 2 * (t + 14) ^ 5 := by
        have hpoly : (t + 16) ^ 5 + (t ^ 5 + 60 * t ^ 4 + 1360 * t ^ 3 + 13920 * t ^ 2 +
            56480 * t + 27072) = 2 * (t + 14) ^ 5 := by ring
        omega
      calc (2 * (k + 1) + 4) ^ 5 = (t + 16) ^ 5 := by rw [ht1]
        _ ≤ 2 * (t + 14) ^ 5 := hstep
        _ = 2 * (2 * k + 4) ^ 5 := by rw [← ht]
        _ ≤ 2 * (2 ^ 30 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ 30 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

/-- Pure-`ℕ` polynomial upper bound on `coreSpaceBase M (rOf M)` for every `M`:
`(2048 * LParam M * (NOf M (rOf M)) ^ (rOf M) + 3) ^ 5 ≤ 2 ^ 155 * (M + 3) ^ 6`. -/
lemma coreSpaceBase_rOf_le (M : ℕ) :
    coreSpaceBase M (rOf M) ≤ 2 ^ 155 * (M + 3) ^ 6 := by
  unfold coreSpaceBase
  set r := rOf M
  set eL := ell M
  have heL1 : 1 ≤ eL := one_le_ell M
  have h2_eL : 2 ^ eL ≤ 4 * M + 4 := by
    have hlt : 2 ^ (eL - 1) < 2 * M + 2 :=
      Nat.pow_pred_clog_lt_self (b := 2) (x := 2 * M + 2) (by decide) (by omega)
    have hmul : 2 ^ eL = 2 ^ (eL - 1) * 2 := by
      conv_lhs => rw [show eL = (eL - 1) + 1 by omega, Nat.pow_succ]
    omega
  have hNr_le : (NOf M r) ^ r ≤ (4 * M + 4) * 2 ^ r := by
    cases hr0 : r with
    | zero => simp
    | succ r' =>
      have hr1 : 1 ≤ r := by omega
      rw [← hr0]
      unfold NOf
      rw [← Nat.pow_mul]
      rcases le_total (ceilDiv eL r) 2 with hle2 | hge2
      · change 2 ^ (max 2 (ceilDiv eL r) * r) ≤ (4 * M + 4) * 2 ^ r
        rw [max_eq_left hle2]
        have hpow : 2 ^ (2 * r) = 2 ^ r * 2 ^ r := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hpow]
        apply Nat.mul_le_mul_right (2 ^ r)
        have hr_log : r ≤ eL := rOf_le_ell M
        calc 2 ^ r ≤ 2 ^ eL := Nat.pow_le_pow_right (by decide) hr_log
          _ ≤ 4 * M + 4 := h2_eL
      · change 2 ^ (max 2 (ceilDiv eL r) * r) ≤ (4 * M + 4) * 2 ^ r
        rw [max_eq_right hge2]
        have hmul_le : ceilDiv eL r * r ≤ eL + r := by
          have := mul_ceilDiv_le (a := eL) hr1
          rw [Nat.mul_comm] at this; omega
        have h1 : 2 ^ (ceilDiv eL r * r) ≤ 2 ^ (eL + r) :=
          Nat.pow_le_pow_right (by decide) hmul_le
        rw [Nat.pow_add] at h1
        exact le_trans h1 (Nat.mul_le_mul_right (2 ^ r) h2_eL)
  have hinner : 2048 * LParam M * (NOf M r) ^ r + 3 ≤ 2 ^ 16 * (M + 3) * (eL * 2 ^ r) := by
    have h1 : 4 * M + 4 ≤ 4 * (M + 3) := by omega
    have h2 : (NOf M r) ^ r ≤ 4 * (M + 3) * 2 ^ r :=
      le_trans hNr_le (Nat.mul_le_mul_right (2 ^ r) h1)
    have h3 : 2048 * LParam M * (NOf M r) ^ r ≤ 32768 * (M + 3) * (eL * 2 ^ r) := by
      unfold LParam
      calc 2048 * (4 * eL) * (NOf M r) ^ r
          ≤ 2048 * (4 * eL) * (4 * (M + 3) * 2 ^ r) := Nat.mul_le_mul_left _ h2
        _ = 32768 * (M + 3) * (eL * 2 ^ r) := by ring
    have hpos : 1 ≤ (M + 3) * (eL * 2 ^ r) :=
      Nat.mul_pos (by omega) (Nat.mul_pos heL1 (Nat.pow_pos (by decide)))
    have h65 : 2 ^ 16 * (M + 3) * (eL * 2 ^ r) =
        32768 * (M + 3) * (eL * 2 ^ r) + 32768 * ((M + 3) * (eL * 2 ^ r)) := by ring
    linarith
  have hpow5 : (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5 ≤
      2 ^ 80 * (M + 3) ^ 5 * (eL ^ 5 * 2 ^ (5 * r)) := by
    have h1 := Nat.pow_le_pow_left hinner 5
    have h2 : (2 ^ 16 * (M + 3) * (eL * 2 ^ r)) ^ 5 =
        2 ^ 80 * (M + 3) ^ 5 * (eL ^ 5 * 2 ^ (5 * r)) := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
    rwa [h2] at h1
  have htail : eL ^ 5 * 2 ^ (5 * r) ≤ 2 ^ 75 * (M + 3) := by
    by_cases hM0 : M = 0
    · subst hM0
      have he1 : eL = 1 := by
        change Nat.clog 2 2 = 1
        decide
      have hr_le : r ≤ 1 := by have := rOf_le_ell 0; omega
      have h5r : 2 ^ (5 * r) ≤ 32 :=
        le_trans (Nat.pow_le_pow_right (by decide) (by omega : 5 * r ≤ 5)) (by decide)
      rw [he1]; norm_num; omega
    · set k := Nat.log 2 M / 2
      have hlog_le_M : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 hM0
      have hM_lt : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by decide) M
      have heL_le : eL ≤ 2 * k + 4 := by
        have h2M2 : 2 * M + 2 ≤ 2 ^ (2 * k + 4) := by
          have h1 : 2 * M + 2 ≤ 4 * 2 ^ (Nat.log 2 M + 1) := by
            have : 1 ≤ 2 ^ (Nat.log 2 M + 1) := Nat.one_le_pow _ _ (by decide)
            omega
          have h2 : 4 * 2 ^ (Nat.log 2 M + 1) = 2 ^ (Nat.log 2 M + 3) := by
            rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; ring
          have h3 : 2 ^ (Nat.log 2 M + 3) ≤ 2 ^ (2 * k + 4) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          omega
        exact Nat.clog_le_of_le_pow h2M2
      have heL5 : eL ^ 5 ≤ 2 ^ 30 * 2 ^ k :=
        le_trans (Nat.pow_le_pow_left heL_le 5) (two_mul_add_four_pow_five_le k)
      have h5r : 2 ^ (5 * r) ≤ 2 ^ 45 * 2 ^ k := by
        by_cases hr9 : r ≤ 9
        · calc 2 ^ (5 * r) ≤ 2 ^ 45 := Nat.pow_le_pow_right (by decide) (by omega)
            _ ≤ 2 ^ 45 * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
        · have hr3 : r ^ 3 ≤ Nat.log 2 M := rOf_pow_le M
          have h10r : 10 * r ≤ r ^ 3 := by
            have h1 : 10 ≤ r * r := by nlinarith
            calc 10 * r ≤ (r * r) * r := Nat.mul_le_mul_right r h1
              _ = r ^ 3 := by ring
          have h5r_k : 5 * r ≤ k := by omega
          calc 2 ^ (5 * r) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h5r_k
            _ ≤ 2 ^ 45 * 2 ^ k := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
      have h2k : 2 ^ k * 2 ^ k ≤ M := by
        rw [← Nat.pow_add]
        exact le_trans (Nat.pow_le_pow_right (by decide) (by omega : k + k ≤ Nat.log 2 M)) hlog_le_M
      calc eL ^ 5 * 2 ^ (5 * r)
          ≤ (2 ^ 30 * 2 ^ k) * (2 ^ 45 * 2 ^ k) := Nat.mul_le_mul heL5 h5r
        _ = 2 ^ 75 * (2 ^ k * 2 ^ k) := by ring
        _ ≤ 2 ^ 75 * M := Nat.mul_le_mul_left _ h2k
        _ ≤ 2 ^ 75 * (M + 3) := Nat.mul_le_mul_left _ (by omega)
  calc (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5
      ≤ 2 ^ 80 * (M + 3) ^ 5 * (eL ^ 5 * 2 ^ (5 * r)) := hpow5
    _ ≤ 2 ^ 80 * (M + 3) ^ 5 * (2 ^ 75 * (M + 3)) := Nat.mul_le_mul_left _ htail
    _ = 2 ^ 155 * (M + 3) ^ 6 := by ring

/-- Bridges the root recursion tree space (at `r = rOf M`) plus top-level scratch (`13 + 3 * n`)
into `outerDecompSpace (outerRecSpaceC C_sp routeC) n M (totalTimeRaw cfg n M (rOf M))`. -/
theorem outerRec_treeSpace_le_outerDecompSpace {cfg : ParamConfig} {C_sp routeC n M : ℕ} :
    let r := rOf M
    13 + 3 * n + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
        (recPerWitSpace cfg M r) M ≤
      outerDecompSpace (outerRecSpaceC C_sp routeC) n M (totalTimeRaw cfg n M r) := by
  intro r
  set A := (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)
  set B := tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3
  set L := LParam M
  set Λ := Lambda cfg M r
  set P := (n + M + 3) ^ 6
  set c29 := (2 ^ 29 : ℕ)
  set c155 := (2 ^ 155 : ℕ)
  have hL4 : 4 ≤ L := four_le_LParam M
  have hLam1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hCT1 : 1 ≤ cfg.CTotal := by
    unfold ParamConfig.CTotal; have := cfg.hu; have := Nat.pow_pos (show 0 < cfg.u by omega) (n := 3)
    omega
  have hP_pos : 1 ≤ P := Nat.pow_pos (by omega)
  have hSB_le : coreSpaceBase M r ≤ c155 * P :=
    le_trans (coreSpaceBase_rOf_le M) (Nat.mul_le_mul_left c155 (Nat.pow_le_pow_left (by omega) 6))
  have h2M3_5 : (2 * M + 3) ^ 5 + 1 ≤ 33 * P := by
    have h1 : 2 * M + 3 ≤ 2 * (n + M + 3) := by omega
    have h2 : (2 * M + 3) ^ 5 ≤ (2 * (n + M + 3)) ^ 5 := Nat.pow_le_pow_left h1 5
    have h3 : (2 * (n + M + 3)) ^ 5 = 32 * (n + M + 3) ^ 5 := by ring
    have h4 : (n + M + 3) ^ 5 ≤ P := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hM1_4 : (M + 1) ^ 4 ≤ P :=
    le_trans (Nat.pow_le_pow_left (by omega : M + 1 ≤ n + M + 3) 4)
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hmodel : modelPerEdge cfg M r routeC ≤ (routeC * c29 + 232) * (A + B + L) :=
    modelPerEdge_le_sum cfg M r routeC
  have hpe_sp : recPerEdgeSpace cfg C_sp M r routeC ≤
      outerRecSpaceC C_sp routeC * ((A + B + L) * P) := by
    unfold recPerEdgeSpace outerRecSpaceC
    change C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * L + 1)) +
        (49 * L + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10) +
        41600 * (M + 1) ^ 4 + 300 * L + 300 ≤
      (C_sp * c155 * (routeC * c29 + 300) + C_sp * 3600 + 46000) * ((A + B + L) * P)
    have ht1 : C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * L + 1)) ≤
        (C_sp * c155 * (routeC * c29 + 300)) * ((A + B + L) * P) := by
      have h49 : 49 * L + 1 ≤ 68 * (A + B + L) := by omega
      have hsum_m : modelPerEdge cfg M r routeC + (49 * L + 1) ≤
          (routeC * c29 + 300) * (A + B + L) := by
        have hdist : (routeC * c29 + 300) * (A + B + L) =
            (routeC * c29 + 232) * (A + B + L) + 68 * (A + B + L) := by ring
        linarith
      calc C_sp * coreSpaceBase M r * (modelPerEdge cfg M r routeC + (49 * L + 1))
          ≤ C_sp * (c155 * P) * ((routeC * c29 + 300) * (A + B + L)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left C_sp hSB_le) hsum_m
        _ = (C_sp * c155 * (routeC * c29 + 300)) * ((A + B + L) * P) := by ring
    have ht2 : (49 * L + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10) ≤
        (3300 * C_sp + 500) * ((A + B + L) * P) := by
      have h49 : 49 * L + 1 ≤ 50 * (A + B + L) := by omega
      have hmid : 2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10 ≤ (66 * C_sp + 10) * P := by
        have h1 : 2 * C_sp * ((2 * M + 3) ^ 5 + 1) ≤ 2 * C_sp * (33 * P) := Nat.mul_le_mul_left _ h2M3_5
        have h2 : 10 ≤ 10 * P := Nat.le_mul_of_pos_right 10 hP_pos
        have h3 : (66 * C_sp + 10) * P = 2 * C_sp * (33 * P) + 10 * P := by ring
        omega
      calc (49 * L + 1) * (2 * C_sp * ((2 * M + 3) ^ 5 + 1) + 10)
          ≤ (50 * (A + B + L)) * ((66 * C_sp + 10) * P) := Nat.mul_le_mul h49 hmid
        _ = (3300 * C_sp + 500) * ((A + B + L) * P) := by ring
    have ht3 : 41600 * (M + 1) ^ 4 + 300 * L + 300 ≤ 42500 * ((A + B + L) * P) := by
      have h1 : 41600 * (M + 1) ^ 4 ≤ 41600 * ((A + B + L) * P) := by
        calc 41600 * (M + 1) ^ 4 ≤ 41600 * P := Nat.mul_le_mul_left _ hM1_4
          _ ≤ 41600 * ((A + B + L) * P) :=
              Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left P (by omega))
      have h2 : 300 * L + 300 ≤ 900 * ((A + B + L) * P) := by
        calc 300 * L + 300 ≤ 900 * (A + B + L) := by omega
          _ ≤ 900 * ((A + B + L) * P) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hP_pos)
      have h3 : 42500 * ((A + B + L) * P) = 41600 * ((A + B + L) * P) + 900 * ((A + B + L) * P) := by ring
      omega
    have hcoeff : C_sp * c155 * (routeC * c29 + 300) + (3300 * C_sp + 500) + 42500 ≤
        C_sp * c155 * (routeC * c29 + 300) + C_sp * 3600 + 46000 := by
      have h1 : 3300 * C_sp ≤ C_sp * 3600 := by linarith
      linarith
    have hcomb := Nat.mul_le_mul_right ((A + B + L) * P) hcoeff
    have hdist : (C_sp * c155 * (routeC * c29 + 300) + (3300 * C_sp + 500) + 42500) * ((A + B + L) * P) =
        (C_sp * c155 * (routeC * c29 + 300)) * ((A + B + L) * P) +
        (3300 * C_sp + 500) * ((A + B + L) * P) + 42500 * ((A + B + L) * P) := by ring
    linarith
  have hpw_sp : 2 * recPerWitSpace cfg M r ≤ outerRecSpaceC C_sp routeC * ((Λ ^ 2 * L ^ 2) * P) := by
    unfold recPerWitSpace outerRecSpaceC
    change 2 * (400 * Λ * L + 400) ≤
      (C_sp * c155 * (routeC * c29 + 300) + C_sp * 3600 + 46000) * ((Λ ^ 2 * L ^ 2) * P)
    have hLam_sq : Λ ≤ Λ ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right Λ hLam1
    have hL_sq : L ≤ L ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right L (by omega)
    have h1 : 2 * (400 * Λ * L + 400) ≤ 1600 * (Λ ^ 2 * L ^ 2) := by
      have hprod : Λ * L ≤ Λ ^ 2 * L ^ 2 := Nat.mul_le_mul hLam_sq hL_sq
      have hpos : 1 ≤ Λ ^ 2 * L ^ 2 := Nat.mul_pos (Nat.pow_pos hLam1) (Nat.pow_pos (by omega))
      have hmul : 800 * (Λ * L) ≤ 800 * (Λ ^ 2 * L ^ 2) := Nat.mul_le_mul_left 800 hprod
      have h800 : 800 ≤ 800 * (Λ ^ 2 * L ^ 2) := Nat.le_mul_of_pos_right 800 hpos
      have hring : 2 * (400 * Λ * L + 400) = 800 * (Λ * L) + 800 := by ring
      linarith
    calc 2 * (400 * Λ * L + 400) ≤ 1600 * (Λ ^ 2 * L ^ 2) := h1
      _ ≤ 1600 * ((Λ ^ 2 * L ^ 2) * P) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hP_pos)
      _ ≤ (C_sp * c155 * (routeC * c29 + 300) + C_sp * 3600 + 46000) * ((Λ ^ 2 * L ^ 2) * P) :=
          Nat.mul_le_mul_right _ (by
            have h0 := Nat.zero_le (C_sp * c155 * (routeC * c29 + 300) + C_sp * 3600)
            linarith)
  have hdep := recDepthBound_le_HDepth cfg (M := M) (r := r) (le_refl M)
  have hTermE : recDepthBound (DOut cfg M r) M * M * recPerEdgeSpace cfg C_sp M r routeC ≤
      outerRecSpaceC C_sp routeC * (M * HDepth cfg M r * (A + B + L)) * P := by
    calc recDepthBound (DOut cfg M r) M * M * recPerEdgeSpace cfg C_sp M r routeC
        ≤ (HDepth cfg M r * M) * (outerRecSpaceC C_sp routeC * ((A + B + L) * P)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right M hdep) hpe_sp
      _ = outerRecSpaceC C_sp routeC * (M * HDepth cfg M r * (A + B + L)) * P := by ring
  have hTermW : 2 * M * recPerWitSpace cfg M r ≤
      outerRecSpaceC C_sp routeC * (M * Λ ^ 2 * L ^ 2) * P := by
    calc 2 * M * recPerWitSpace cfg M r
        = M * (2 * recPerWitSpace cfg M r) := by ring
      _ ≤ M * (outerRecSpaceC C_sp routeC * ((Λ ^ 2 * L ^ 2) * P)) := Nat.mul_le_mul_left M hpw_sp
      _ = outerRecSpaceC C_sp routeC * (M * Λ ^ 2 * L ^ 2) * P := by ring
  have hTerm0 : 13 + 3 * n + 3 ≤ outerRecSpaceC C_sp routeC * 1 * P := by
    have h1 : n + M + 3 ≤ P := by
      calc n + M + 3 = (n + M + 3) ^ 1 := (pow_one _).symm
        _ ≤ P := Nat.pow_le_pow_right (by omega) (by decide)
    have h2 : 16 + 3 * n ≤ 6 * P := by omega
    have h3 : 6 ≤ outerRecSpaceC C_sp routeC := by
      unfold outerRecSpaceC
      change 6 ≤ C_sp * c155 * (routeC * c29 + 300) + C_sp * 3600 + 46000
      have h0 := Nat.zero_le (C_sp * c155 * (routeC * c29 + 300) + C_sp * 3600)
      linarith
    calc 13 + 3 * n + 3 ≤ 6 * P := by omega
      _ ≤ outerRecSpaceC C_sp routeC * 1 * P := by
          rw [mul_one]; exact Nat.mul_le_mul_right P h3
  have hTot_ge : M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2 ≤ totalTimeRaw cfg n M r := by
    unfold totalTimeRaw
    change M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2 ≤
      cfg.CTotal * (n + M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2)
    calc M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2
        ≤ 1 * (n + M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2) := by omega
      _ ≤ cfg.CTotal * (n + M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2) :=
          Nat.mul_le_mul_right _ hCT1
  unfold outerDecompSpace recTreeSpace
  calc 13 + 3 * n + (recDepthBound (DOut cfg M r) M * M * recPerEdgeSpace cfg C_sp M r routeC +
          2 * M * recPerWitSpace cfg M r + 3)
      = (13 + 3 * n + 3) +
          recDepthBound (DOut cfg M r) M * M * recPerEdgeSpace cfg C_sp M r routeC +
          2 * M * recPerWitSpace cfg M r := by ring
    _ ≤ outerRecSpaceC C_sp routeC * 1 * P +
          outerRecSpaceC C_sp routeC * (M * HDepth cfg M r * (A + B + L)) * P +
          outerRecSpaceC C_sp routeC * (M * Λ ^ 2 * L ^ 2) * P :=
        Nat.add_le_add (Nat.add_le_add hTerm0 hTermE) hTermW
    _ = outerRecSpaceC C_sp routeC *
          ((M * HDepth cfg M r * (A + B + L) + M * Λ ^ 2 * L ^ 2) + 1) * P := by ring
    _ ≤ outerRecSpaceC C_sp routeC * (totalTimeRaw cfg n M r + 1) * P :=
        Nat.mul_le_mul_right P (Nat.mul_le_mul_left _ (Nat.add_le_add_right hTot_ge 1))

end MinCostFlow.ExpanderDecomp
