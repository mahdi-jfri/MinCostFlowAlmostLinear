module

public import MinCostFlow.MinRatio.OrdSolverRepFull
public import MinCostFlow.MinRatio.OrdShiftStepKFBL
public import MinCostFlow.MinRatio.SolverInitWiredGrow
import Mathlib.Tactic

/-!
# `KFBL` solver representation and deep-shift invariant bundle (`OrdSolverRepFullKFBL`)

Wraps `solverStateRepFull` (`OrdSolverRepFull.lean`) with the two extra invariants needed by
`ShiftLevelStepSpecWKFBL` and `ShiftDeepChainSyncSpecWExtKFBL` without altering `solverStateRepFull`:
* `SolverLevelCapsInv P V G.n (initTargetCap cfg G)` (`SolverLevelCapsInv.lean`);
* a caller-supplied chain invariant `DeepInv : ChainState cfg.T cfg.P → Prop` bundled in
  `DeepShiftChainInvHyps` (instantiated in the dry run by `DryChainLenGridInv J`).

Also defines `SolverInitStepSpecCreditKFBL` (extending `SolverInitStepSpecCredit` with
`SolverLevelCapsInv P V G.n (initTargetCap cfg G)`) and `solverInitStepSpecCreditKFBL_of_wired`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program

/-- Credit-bearing modular contract for the `Init` procedure under the `KFBL` layout contract:
extends `SolverInitStepSpecCredit` with `SolverLevelCapsInv P V G.n (initTargetCap cfg G)`. -/
@[expose] def SolverInitStepSpecCreditKFBL {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp : ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (initProc : ℕ) (initSpace initFixed toolMul treeMul : ℕ) : Prop :=
  let L := F.limbs
  let P := F.fmt.precision
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  ∃ body, p.procs[initProc]? = some body ∧
    ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ x ∈ args, x < 2 ^ w) →
      minRatioInitPreWithV F G m V (1 / (2 : ℝ) ^ k) cfg.α args mem →
      ZeroFrom mem (heapArg args) →
      heapArg args + initSpace < 2 ^ w →
      ∃ finalHeap cost out tok,
        Runs w p ω body (startState args mem pos) (.returned finalHeap) out cost ∧
        let s0 := (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).init G
          (readVector mem (args.getD 1 0) F.fmt.limbBits L P m)
          (readVector mem (args.getD 2 0) F.fmt.limbBits L P m)
        MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G
          F.fmt.limbBits L P s0 ∧
        Rrep.rep (heapArg args) s0 tok out.mem ∧
        SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tok out.mem ∧
        tok.intCap = initTargetCap cfg G ∧
        SolverTreeNumericInv P s0 tok ∧
        Rrep.Respects (fun _ => False) (heapArg args) initSpace mem finalHeap (heapArg args) tok out.mem ∧
        cost + Rrep.phi (heapArg args) tok out.mem ≤
          initFixed + toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates

/-- Discharges `SolverInitStepSpecCreditKFBL` directly from `ordSolverInitWired_runs`. -/
theorem solverInitStepSpecCreditKFBL_of_wired {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp : ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (initProc initConcreteProc overwriteProc copyWords initSpace initFixed toolMul
      treeMul : ℕ)
    (hInitAt : p.procs[initProc]? = some (solverInitWiredBody initConcreteProc overwriteProc copyWords))
    (hFmt4 : F.fmt.limbBits = 4)
    (hRun : ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ x ∈ args, x < 2 ^ w) → minRatioInitPreWithV F G m V (1 / (2 : ℝ) ^ k) cfg.α args mem →
      ZeroFrom mem (heapArg args) → heapArg args + initSpace < 2 ^ w →
      ∃ finalHeap cost out tok,
        let L := F.limbs; let P := F.fmt.precision
        let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
        let s0 := Chain.Ordered.algorithm2_init cfg G
          (readVector mem (args.getD 1 0) 4 L P m) (readVector mem (args.getD 2 0) 4 L P m)
        Runs w p ω (solverInitWiredBody initConcreteProc overwriteProc copyWords)
          (startState args mem pos) (.returned finalHeap) out cost ∧
        Rrep.rep (heapArg args) s0 tok out.mem ∧
        SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tok out.mem ∧
        tok.intCap = initTargetCap cfg G ∧
        SolverTreeNumericInv P s0 tok ∧ heapArg args ≤ finalHeap ∧ finalHeap ≤ heapArg args + initSpace ∧
        ZeroFrom out.mem finalHeap ∧ (∀ a < heapArg args, out.mem a = mem a) ∧
        (∀ a, Rrep.foot (heapArg args) tok a → heapArg args ≤ a ∧ a < finalHeap) ∧
        cost + Rrep.phi (heapArg args) tok out.mem ≤
          initFixed + toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates) :
    SolverInitStepSpecCreditKFBL F cfg G m V psi k epsExp Rcore p initProc initSpace initFixed
      toolMul treeMul := by
  refine ⟨solverInitWiredBody initConcreteProc overwriteProc copyWords, hInitAt,
    fun args mem pos ω hargsW hpre hz hroom => ?_⟩
  obtain ⟨finalHeap, cost, out, tok, hr, hrep, hcaps, hcap, hnum, hlo, hhi, hzOut, hframe, hfoot,
      hcost⟩ := hRun args mem pos ω hargsW hpre hz hroom
  refine ⟨finalHeap, cost, out, tok, hr, ?_, ?_, ?_, hcap, ?_,
    ⟨hlo, hhi, hzOut, fun a ha _ => hframe a ha, fun a ha => Or.inr (hfoot a ha)⟩, ?_⟩
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using
      (algorithm2_init_stateFits (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (h := 4)
        (L := F.limbs) (P := F.fmt.precision))
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hrep
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hcaps
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hnum
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hcost

/-- Bundled preservation and model-discharge hypotheses for a chain invariant `DeepInv` needed to
discharge `ShiftDeepModelInv` inside `ShiftLevelStepSpecWKFBL` at every non-terminal shift. -/
structure DeepShiftChainInvHyps (w : ℕ) (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (k wordExp stretchPrec : ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) : Prop where
  init : ∀ g₀ ℓ₀ : ℕ → ℝ,
    LengthsWithin G F.rangeExponent ℓ₀ →
    (∀ e ∈ G.E, ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ F.fmt.precision = ℓ₀ e) →
    DeepInv (Ordered.algorithm2_init cfg G g₀ ℓ₀).chain
  preLoop : ∀ (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ),
    OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model →
    model.extG = G →
    RefreshBatch G U →
    (∀ e ∈ G.E, (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ F.rangeExponent) →
    (∀ e ∈ G.E, ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ F.fmt.precision = lVec e) →
    (∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → gVec e = model.extg e ∧ lVec e = model.extℓ e) →
    DeepInv model.chain →
    DeepInv (alg2PreLoopState cfg model U gVec lVec).chain
  shift : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch → DeepInv ch →
    ∀ i ≤ cfg.P.d, DeepInv (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i).1
  toModel : ∀ (stM : Alg2State cfg) (i : Fin (cfg.P.d + 1)), i.val < cfg.P.d →
    Chain.Ordered.ShiftLoopChainInv cfg stM.chain → DeepInv stM.chain →
    ShiftDeepModelInv w F.limbs F.fmt.precision wordExp stretchPrec stM i

/-- **The `KFBL` solver representation:** wraps `solverStateRepFull` with
`SolverLevelCapsInv P V G.n (initTargetCap cfg G)` and `DeepInv model.chain`, keeping the exact
same witness type `τ`, footprint `foot`, and potential `phi`. -/
@[expose] noncomputable def solverStateRepFullKFBL (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (DeepInv : ChainState cfg.T cfg.P → Prop) :
    DSRep (Alg2State cfg) where
  τ := (SolverToken cfg L Rcore × ℕ) × (ℕ × ℕ)
  rep root model tok mem :=
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).rep
      root model tok mem ∧
    SolverLevelCapsInv P V G.n (initTargetCap cfg G) model tok.1.1 mem ∧
    DeepInv model.chain
  foot root tok :=
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
      root tok
  phi root tok mem :=
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).phi
      root tok mem

/-- `solverStateRepFullKFBL` is local: `solverStateRepFull` is local, `DeepInv` does not read
memory, and `SolverLevelCapsInv` reads only addresses inside `solverStateRep.foot`
(`LevelMetaFoot.mem_foot`). -/
theorem solverStateRepFullKFBL_local (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ)
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    (DeepInv : ChainState cfg.T cfg.P → Prop) :
    (solverStateRepFullKFBL cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore
      DeepInv).Local := by
  intro b s x mem mem' hag
  obtain ⟨hrepF, hphiF⟩ := solverStateRepFull_local cfg κ G L P m V psi k epsExp drainUnit unit
    toolMul treeMul hlocalCore b s x mem mem' hag
  refine ⟨fun ⟨hF, hCaps, hDeep⟩ => ⟨hrepF hF, ?_, hDeep⟩, hphiF⟩
  have hPres : PreservesLevelMeta x.1.1 x.1.1 mem mem' :=
    (PreservesLevelMeta.refl x.1.1 mem).congr_mem_right fun a ht =>
      (hag a (LevelMetaFoot.mem_foot hF.1.1 ht)).symm
  exact hPres.to_capsInv hCaps rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl

/-- The potential of `solverStateRepFullKFBL` is definitionally that of `solverStateRepFull`. -/
theorem solverStateRepFullKFBL_phi_eq {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {root : ℕ} {model : Alg2State cfg} {tok : (SolverToken cfg L Rcore × ℕ) × (ℕ × ℕ)} {mem : ℕ → ℕ}
    (hrep : (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root model tok.1
      mem)
    (hrc : tok.2.1 = runtimeCredit cfg model)
    (htc : tok.2.2 = treeCredit cfg model) :
    (solverStateRepFullKFBL cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore
      DeepInv).phi root tok mem =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok.1.1 mem +
        unit * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain +
          chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain) +
        unit * fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain +
        toolMul * runtimeCredit cfg model + treeMul * treeCredit cfg model :=
  solverStateRepFull_phi_eq (κ := κ) (G := G) hrep hrc htc

end MinCostFlow.MinRatio

end
