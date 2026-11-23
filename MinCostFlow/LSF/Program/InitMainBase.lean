module

public import MinCostFlow.LSF.Program.InitGlue

/-!
# Helpers for the main path of the init driver

The places above the heap `H` of the tree phase are those of `V.withH H`. This file proves the
facts about `V.withH H` that `main_wp` (`InitMain.lean`) uses, and the budget facts between the
segments: the cost of the decomposition segment grows with the count `cnt ≤ n₀`, so the budget of
`main_wp`, taken at `cnt = n₀`, covers every segment. Each budget fact is a small lemma, so that
`omega` runs in a small context.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- The numbers of the places, with the heap pointer `H`. -/
def InitVals.withH (V : InitVals) (H : ℕ) : InitVals := { V with H := H }

/-- The input facts do not mention `H`, so they hold for `V.withH H` too. -/
theorem SegBIn.withH {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {V : InitVals} {lenArr wtArr kk : ℕ} {mem : ℕ → ℕ}
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem) (H : ℕ) :
    SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp (V.withH H) lenArr wtArr kk mem := by
  cases S; constructor <;> assumption

/-- The work area ends at `useEnd`, and the scratch places lie below it. -/
lemma InitVals.useEnd_ge (V : InitVals) :
    V.thBase + 8 * V.n0 ≤ V.wBase ∧
    wsPt V.idPtr V.n0 V.tM V.m0 V.LB 18 + V.m0 = V.wBase ∧ V.wBase ≤ V.useEnd ∧
    V.endA + 6 ≤ V.lsstHeap := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s26, s27,
    s28, s29, s30, s31, s32⟩ := V.scratch_order
  have := V.segB_le.2.2.2.2.2.2
  refine ⟨by omega, s32, by unfold InitVals.useEnd; omega, this⟩

lemma segDCost_mono (V : InitVals) {c₁ c₂ : ℕ} (hc : c₁ ≤ c₂) :
    segDCost V c₁ ≤ segDCost V c₂ := by
  simp only [segDCost, decompPhaseCost, decompArgs_ofVals, List.getD_cons_succ,
    List.getD_cons_zero]
  omega

lemma prep_cnt_le {w : ℕ} {G₀ : MGraph} {args : List ℕ} {mem mem₁ : ℕ → ℕ} {cnt : ℕ}
    (h₁ : (prepStageContract w G₀).post args mem cnt mem₁) : cnt ≤ G₀.n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -⟩ := h₁
  exact hc

lemma segDCost_withH (V : InitVals) (H c : ℕ) : segDCost (V.withH H) c = segDCost V c := by
  simp only [segDCost, decompPhaseCost, decompArgs_ofVals, List.getD_cons_succ,
    List.getD_cons_zero]
  rfl

lemma segCCost_withH (V : InitVals) (H : ℕ) : segCCost (V.withH H) = segCCost V := by
  simp only [segCCost, orderPhaseCost, OrderLayout.ofVals, OrderLayout.args, List.getD_cons_succ,
    List.getD_cons_zero]
  rfl

lemma segECost_withH (V : InitVals) (H : ℕ) : segECost (V.withH H) = segECost V := by
  simp only [segECost, fPhaseCost, FLayout.ofVals, FLayout.ofDecomp, FLayout.args,
    List.getD_cons_succ, List.getD_cons_zero]
  rfl

/-- The budget of segment C, after segments A and B. -/
lemma budget_segC (V : InitVals) {H Bt B : ℕ}
    (hB : segACost V.n0 + segBCost V.n0 V.m0 Bt + segCCost V + segDCost V V.n0 + segECost V +
      segFCost ≤ B) :
    segCCost (V.withH H) ≤ B - segACost V.n0 - segBCost V.n0 V.m0 Bt := by
  rw [segCCost_withH]
  omega

/-- The budget of segment D, after segments A, B and C. -/
lemma budget_segD (V : InitVals) {H cnt Bt B : ℕ} (hcn : cnt ≤ V.n0)
    (hB : segACost V.n0 + segBCost V.n0 V.m0 Bt + segCCost V + segDCost V V.n0 + segECost V +
      segFCost ≤ B) :
    segDCost (V.withH H) cnt ≤ B - segACost V.n0 - segBCost V.n0 V.m0 Bt - segCCost (V.withH H) := by
  have := segDCost_mono V hcn
  have e := segDCost_withH V H cnt
  have e'' := segCCost_withH V H
  omega

/-- The budget of segment E, after segments A to D. -/
lemma budget_segE (V : InitVals) {H cnt Bt B : ℕ} (hcn : cnt ≤ V.n0)
    (hB : segACost V.n0 + segBCost V.n0 V.m0 Bt + segCCost V + segDCost V V.n0 + segECost V +
      segFCost ≤ B) :
    segECost (V.withH H) ≤ B - segACost V.n0 - segBCost V.n0 V.m0 Bt - segCCost (V.withH H) -
      segDCost (V.withH H) cnt := by
  have := segDCost_mono V hcn
  have e := segDCost_withH V H cnt
  have e' := segECost_withH V H
  have e'' := segCCost_withH V H
  omega

/-- The budget of segment F, after segments A to E. -/
lemma budget_segF (V : InitVals) {H cnt Bt B : ℕ} (hcn : cnt ≤ V.n0)
    (hB : segACost V.n0 + segBCost V.n0 V.m0 Bt + segCCost V + segDCost V V.n0 + segECost V +
      segFCost ≤ B) :
    segFCost ≤ B - segACost V.n0 - segBCost V.n0 V.m0 Bt - segCCost (V.withH H) -
      segDCost (V.withH H) cnt - segECost (V.withH H) := by
  have := segDCost_mono V hcn
  have e := segDCost_withH V H cnt
  have e' := segECost_withH V H
  have e'' := segCCost_withH V H
  omega

/-- The budget left at the end of the main path. -/
lemma budget_fin (V : InitVals) {H cnt Bt B : ℕ} (hcn : cnt ≤ V.n0) :
    B - (segACost V.n0 + segBCost V.n0 V.m0 Bt + segCCost V + segDCost V V.n0 + segECost V +
      segFCost) ≤ B - segACost V.n0 - segBCost V.n0 V.m0 Bt - segCCost (V.withH H) -
      segDCost (V.withH H) cnt - segECost (V.withH H) - segFCost := by
  have := segDCost_mono V hcn
  have e := segDCost_withH V H cnt
  have e' := segECost_withH V H
  have e'' := segCCost_withH V H
  omega

/-- After the forest phase, the root count at the start of the `F` block and the first entry of
the vertex list are words: the count is at most `n` (`rootList_length_le`), the entry is below
`vCap` (`FPhaseIn.hvL`), and both `n` and `vCap` lie below the end of the work area. -/
lemma fPhase_words {w h bG bA bW : ℕ} {X : FLayout} {mem₅ mem₆ : ℕ → ℕ} {v₆ : ℕ}
    (FI : FPhaseIn w h X mem₅) (h₆ : (fPhaseContract w h bG bA bW).post X.args mem₅ v₆ mem₆) :
    mem₆ X.fAnc < 2 ^ w ∧ mem₆ X.vListPtr < 2 ^ w := by
  have l1 := FI.l1; have l2 := FI.l2; have l3 := FI.l3; have l4 := FI.l4; have l12 := FI.l12
  have l20 := FI.l20; have hn := FI.hn
  have hdg : dynGraphSize X.vCap X.eCap = 4 + 7 * X.vCap + 9 * X.eCap := rfl
  have hfs : fAncSize X.vCap = 6 + 5 * X.vCap := rfl
  have hws : wWorkSize X.n X.logCap = X.n * (3 * X.logCap) + 3 * X.n := rfl
  obtain ⟨v₁, m₁, v₂, m₂, v₃, h₁, h₂, h₃⟩ := fPhase_post h₆
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₁, -, -, hfr₁⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  obtain ⟨_, _, _, _, _, _, heq₂, -, hfr₂, hR, -⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₃, -, -, hfr₃, -⟩ := h₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  have hR0 : mem₆ X.fAnc = (rootList (fun x => m₁ (X.vListPtr + x)) (fun x => m₁ (X.inR + x))
      X.n).length := by
    rw [hfr₃ _ (Or.inl (by omega)) (Or.inl (by omega))]
    simpa [fOffRCount] using hR
  have hlen := rootList_length_le (fun x => m₁ (X.vListPtr + x)) (fun x => m₁ (X.inR + x)) X.n
  have hnw : X.n < 2 ^ w := by
    have : X.n ≤ wWorkSize X.n X.logCap := by rw [hws]; omega
    omega
  refine ⟨by omega, ?_⟩
  have hv := (FI.hvL 0 hn)
  rw [Nat.add_zero] at hv
  rw [hfr₃ _ (Or.inl (by omega)) (Or.inr (by omega)), hfr₂ _ (Or.inr (by omega)),
    hfr₁ _ (Or.inr (by omega))]
  omega

end

end MinCostFlow.LSF.Program
