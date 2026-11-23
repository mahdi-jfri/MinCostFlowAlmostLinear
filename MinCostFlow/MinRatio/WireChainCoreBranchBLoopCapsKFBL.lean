module

public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
import WordRAM.Tactic

/-!
# The caps of the model invariant of the Branch B loop (`WireChainCoreBranchBLoopCapsKFBL`)

`UpdateCoreModelInv` gives the model invariant of the level loop (`UpdateLoopModelInv`) at caps
`vcOf`, `ecOf` that it names. The run of the loop (`wireBranchBLoopKFBL_runs`) asks for the same
invariant at the caps `fun _ => vCap` and `fun _ => eCap` of `SolverLevelCapsAt`. The two families
agree at every level below `d`, since the graphs of these levels are stored with both
(`dynGraphAt_caps_eq`).

The invariant reads the caps only at levels below `d`: at the current level `idx` when levels are
left, and at `idx + 1` only when `idx + 1 < d`. So `updateLoopModelInv_caps_congr` moves it from one
family of caps to another that agrees with it below `d`. `updateLoopModelInv_of_coreModelInv` uses
it to give the invariant at the start of the loop, at the caps of `SolverLevelCapsAt`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The model invariant of the level loop depends on the caps only at the levels below `d`. -/
theorem updateLoopModelInv_caps_congr {w L P wordExp stretchPrec : ℕ} {cfg : Alg2Config}
    {vcOf ecOf vc' ec' : ℕ → ℕ} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ}
    (hv : ∀ j < cfg.P.d, vcOf j = vc' j) (he : ∀ j < cfg.P.d, ecOf j = ec' j) :
    ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEnc : ℕ) (oldOrd : ℕ → List End),
      idx + rem = cfg.P.d →
      UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf origLen ℓ' g' rem idx st curG curU
        curEnc oldOrd →
      UpdateLoopModelInv w L P wordExp stretchPrec vc' ec' origLen ℓ' g' rem idx st curG curU
        curEnc oldOrd := by
  intro rem
  induction rem with
  | zero => intro idx st curG curU curEnc oldOrd _ h; exact h
  | succ rem ih =>
    intro idx st curG curU curEnc oldOrd hsum h
    have hidx : idx < cfg.P.d := by omega
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
    refine ⟨a1, a2, by rw [← hv idx hidx, ← he idx hidx]; exact a3, a4,
      fun e hE => by rw [← he idx hidx]; exact a5 e hE, ?_⟩
    split_ifs at a6 ⊢ with hT
    · exact a6
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := a6
      refine ⟨b1, b2, b3, b4, b5, fun hlt => ?_, ih _ _ _ _ _ _ (by omega) b7⟩
      obtain ⟨c1, c2, c3⟩ := b6 hlt
      refine ⟨c1, fun u hu => ?_, c3⟩
      rw [← he idx hidx, ← he (idx + 1) hlt]
      exact c2 u hu

/-- The model invariant of the level loop at its start (level `0`, all `d` levels left), at the
caps `(vCap, eCap)` of `SolverLevelCapsAt`. `UpdateCoreModelInv` gives it at its own caps, which
agree with `(vCap, eCap)` below `d`, since both store the graph of each level at the same
address. -/
theorem updateLoopModelInv_of_coreModelInv
    {w L P m epsExp wordExp stretchPrec vCap eCap g l : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B) :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let g' := fun e' => gVec (tr.2.2.1 e')
    let st0 : ChainState cfg.T cfg.P :=
      { model.chain with
        recUpdates := fun j =>
          if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
    UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap)
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) ℓ' g' cfg.P.d 0 st0
      (G0.applyBatch U_int) U_int (G0.batchEnc U_int) (st0.levelOrd 0) := by
  intro tr U_int G0 gVec lVec ℓ' g' st0
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, hLoop⟩, _⟩ := hModelInv
  exact updateLoopModelInv_caps_congr
    (fun j hj => (dynGraphAt_caps_eq (hLev j hj).1 (hCaps0 j hj)).1)
    (fun j hj => (dynGraphAt_caps_eq (hLev j hj).1 (hCaps0 j hj)).2) cfg.P.d 0 _ _ _ _ _
    (by omega) hLoop

end MinCostFlow.MinRatio
