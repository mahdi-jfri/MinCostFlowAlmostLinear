module

public import MinCostFlow.NarrowProg.Stage0Feas
public import MinCostFlow.NarrowProg.Stage0Res
public import MinCostFlow.NarrowTop.MainCalls

/-!
# Concrete `Stage0CallsPkg` instance (`stage0CallsPkg`)

Instantiates `Stage0CallsPkg` (`MinCostFlow/NarrowTop/MainCalls.lean`) from the proved Stage 0
modules `stage0FeasMod` (`MinCostFlow/NarrowProg/Stage0Feas.lean`) and `stage0ResMod`
(`MinCostFlow/NarrowProg/Stage0Res.lean`), using disjoint `.mainAux` procedure indices
`100..117` (feasibility call, entry `117`) and `200..221` (residual call, entry `221`).
-/

@[expose] public section

open WordRAM WordRAM.Sep MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg
  MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowTop

/-- Procedure names for `stage0FeasMod` inside `narrowProgram` (`.mainAux 100..117`). -/
def topStage0FeasNames : Stage0FeasNames NarrowTopName where
  padCopy := .mainAux 100
  limbsCmp := .mainAux 101
  canonLen := .mainAux 102
  copyFlowLimbs := .mainAux 103
  feasPass1 := .mainAux 104
  feasArtEmit := .mainAux 105
  feasArtPass := .mainAux 106
  feasArtBoth := .mainAux 107
  writeStage1Hdr := .mainAux 108
  feasBuild := .mainAux 109
  feasCheckOne := .mainAux 110
  feasSatCheck := .mainAux 111
  feasScatter := .mainAux 112
  feasPost := .mainAux 113
  feasPostWrap := .mainAux 114
  feasRun := .mainAux 115
  feasWork := .mainAux 116
  stage0Feas := .mainAux 117
  stage1Circ := .stage1 0

/-- Procedure names for `stage0ResMod` inside `narrowProgram` (`.mainAux 200..221`). -/
def topStage0ResNames : Stage0ResNames NarrowTopName where
  padCopy := .mainAux 200
  canonLen := .mainAux 201
  limbsSub := .mainAux 202
  copyFlowLimbs := .mainAux 203
  resCostSum := .mainAux 204
  resEmit := .mainAux 205
  resCopyCost := .mainAux 206
  resRevSign := .mainAux 207
  resFwdEmit := .mainAux 208
  resRevEmit := .mainAux 209
  resFwdSub := .mainAux 210
  resFwdStep := .mainAux 211
  resRevStep := .mainAux 212
  resPassFwd := .mainAux 213
  resPassRev := .mainAux 214
  writeStage1Hdr := .mainAux 215
  resBuild := .mainAux 216
  resScatterSlice := .mainAux 217
  resScatter := .mainAux 218
  resRun := .mainAux 219
  resWork := .mainAux 220
  stage0Res := .mainAux 221
  stage1Circ := .stage1 0

private theorem stage0FeasSpace_defeq (m L : ℕ) :
    stage0FeasSpace m L = NarrowProg.stage0FeasSpace m L := rfl

private theorem stage0ResSpace_defeq (m L totCost : ℕ) :
    stage0ResSpace m L totCost = NarrowProg.stage0ResSpace m L totCost := rfl

private theorem totCostLimbs_defeq (I : Instance) :
    totCostLimbs I = NarrowProg.totCostLimbs I := rfl

private theorem stage0FeasSpec_pre_eq (w : ℕ) (S : ℕ → ℕ → ℕ) (d : Stage0FeasData) (args : List ℕ) :
    (stage0FeasSpec w S).pre d args =
      (NarrowProg.stage0FeasSpec w S).pre ⟨d.I, d.hv, d.hiso, d.act, d.L, d.hLge, d.outBuf⟩ args := by
  unfold stage0FeasSpec NarrowProg.stage0FeasSpec
  dsimp only
  simp only [stage0FeasSpace_defeq]

private theorem stage0FeasSpec_post_le (w : ℕ) (S : ℕ → ℕ → ℕ) (d : Stage0FeasData) (args : List ℕ)
    (v : ℕ) :
    (NarrowProg.stage0FeasSpec w S).post ⟨d.I, d.hv, d.hiso, d.act, d.L, d.hLge, d.outBuf⟩ args v ≤
      (stage0FeasSpec w S).post d args v := by
  unfold stage0FeasSpec NarrowProg.stage0FeasSpec
  dsimp only
  simp only [stage0FeasSpace_defeq]
  refine iSup_le fun pEdges => iSup_le fun pLabels => iSup_le fun pShCapBuf =>
    iSup_le fun pShCapLen => iSup_le fun pShDemBuf => iSup_le fun pShDemSign =>
    iSup_le fun pShDemLen => iSup_le fun pFeasOut => iSup_le fun h =>
    iSup_le fun ok => iSup_le fun pFeasFlow => iSup_le fun f => ?_
  refine le_trans ?_ (le_iSup_of_le pEdges (le_iSup_of_le pLabels (le_iSup_of_le pShCapBuf
    (le_iSup_of_le pShCapLen (le_iSup_of_le pShDemBuf (le_iSup_of_le pShDemSign
    (le_iSup_of_le pShDemLen (le_iSup_of_le pFeasOut (le_iSup_of_le h
    (le_iSup_of_le ok (le_iSup_of_le pFeasFlow (le_iSup_of_le f le_rfl))))))))))))
  apply Assn.mul_le_mul_of_le _ le_rfl
  apply Assn.mul_le_mul_of_le _ le_rfl
  apply Assn.mul_le_mul_of_le _ le_rfl
  apply Assn.mul_le_mul_of_le le_rfl
  split
  · exact le_rfl
  · exact Assn.one_le_gc

private theorem stage0ResSpec_pre_eq (w : ℕ) (S : ℕ → ℕ → ℕ) (d : Stage0ResData) (args : List ℕ) :
    (stage0ResSpec w S).pre d args =
      (NarrowProg.stage0ResSpec w S).pre ⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge, d.outBuf⟩ args := by
  unfold stage0ResSpec NarrowProg.stage0ResSpec
  dsimp only
  simp only [stage0ResSpace_defeq, totCostLimbs_defeq]

private theorem stage0ResSpec_post_eq (w : ℕ) (S : ℕ → ℕ → ℕ) (d : Stage0ResData) (args : List ℕ)
    (v : ℕ) :
    (stage0ResSpec w S).post d args v =
      (NarrowProg.stage0ResSpec w S).post ⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge, d.outBuf⟩ args v := by
  unfold stage0ResSpec NarrowProg.stage0ResSpec
  dsimp only
  simp only [stage0ResSpace_defeq, totCostLimbs_defeq]

/-- Proved instance of `Stage0CallsPkg` from `stage0FeasMod` and `stage0ResMod`. -/
def stage0CallsPkg : Stage0CallsPkg where
  feasMod := stage0FeasMod topStage0FeasNames
  resMod := stage0ResMod topStage0ResNames
  feasEntry := 117
  resEntry := 221
  feas_names := by
    intro n hn
    simp only [stage0FeasMod, Module.names, List.map, topStage0FeasNames,
      List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, by omega, by omega⟩
  res_names := by
    intro n hn
    simp only [stage0ResMod, Module.names, List.map, topStage0ResNames,
      List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, rfl, by omega⟩
  feas_nodup := by decide
  res_nodup := by decide
  feas_noRand := stage0FeasMod_noRand topStage0FeasNames
  res_noRand := stage0ResMod_noRand topStage0ResNames
  aFeas := 2500
  aRes := 2500
  feas_meets := fun w p idx S B _ hB_mono hp hstage1 => by
    obtain ⟨body, hbody, htri⟩ := stage0FeasMod_meets_direct (w := w) (p := p) (idx := idx)
      (S := S) (B := B) (names := topStage0FeasNames) hB_mono hp hstage1
    refine ⟨body, hbody, fun d args => ?_⟩
    have h := htri ⟨d.I, d.hv, d.hiso, d.act, d.L, d.hLge, d.outBuf⟩ args
    refine h.conseq (fun ρ => ?_) (fun o _ => ?_)
    · simp only [Spec.withCost, stage0FeasSpec_pre_eq]; exact Assn.le_mul_gc _
    · exact (stage0FeasSpec_post_le w S d args o.value).trans (Assn.le_mul_gc _)
  res_meets := fun w p idx S B _ hB_mono hp hstage1 => by
    obtain ⟨body, hbody, htri⟩ := stage0ResMod_meets_direct (w := w) (p := p) (idx := idx)
      (S := S) (B := B) (names := topStage0ResNames) hB_mono hp hstage1
    refine ⟨body, hbody, fun d args => ?_⟩
    have h := htri ⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge, d.outBuf⟩ args
    simpa only [Spec.withCost, ← stage0ResSpec_pre_eq, ← stage0ResSpec_post_eq] using h

end MinCostFlow.NarrowTop
