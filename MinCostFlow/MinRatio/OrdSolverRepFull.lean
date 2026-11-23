module

public import MinCostFlow.MinRatio.OrdSolverReachInv
public import MinCostFlow.MinRatio.OrdSolverReached
public import MinCostFlow.MinRatio.OrdSolverToolCredit
public import MinCostFlow.MinRatio.ShiftInitQuota
import Mathlib.Tactic

/-!
# One representation for the solver

The solver has two wrappers of `solverStateRep`: `solverStateRepInv` (`OrdSolverReachInv.lean`)
adds the invariants of the reachable states, and `solverStateRepShift`
(`OrdSolverShiftPotential.lean`) adds the shift potential and the forward potential, with a
ghost for the forward potential. This file puts them together in `solverStateRepFull`, and adds
the facts that hold only on reached states:
* `OrdSolverReached`: a valid history reaches the state (`OrdSolverReached.lean`);
* the bound on the next fresh name (`alg2_nextFresh_le_with`).
The recourse bound `FwdBoundNat` on the chain is already a conjunct of `solverStateRepShift`. The
recourse bound on the chain before the shift loop of the next `Update` is not a property of the
state alone, since it depends on the batch. It follows from `OrdSolverReached`
(`OrdSolverReached.preLoop_fwd`).

The footprint is that of `solverStateRep`, and the potential is that of `solverStateRepShift`:
the potential of `solverStateRep` plus `unit` times the unused shift quota, the deposit, and the
forward potential.

* `solverStateRepFull_local`: the representation is local.
* `solverStateRepFull_phi_eq`: its potential on a represented state.
* `fwdBoundNat_init` and `solverStateRepFull_phi_init_le`: the state that `Init` builds meets
  `FwdBoundNat`, and its potential is at most that of `solverStateRep` plus
  `unit · (d + 1) ⌊(10 Ψ k)^{d+1}⌋` (`algorithm2_init_potentials`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM IPM.Machine SparseCore.Program

/-- The facts of a reached state that the solver keeps besides `solverStateRepShift`: the
reachable-state invariant `OrdSolverReachInv`, the state is reached (`OrdSolverReached`),
the bound on the next fresh name, and the fixed internal-table capacity
`tok.intCap = initTargetCap cfg G` allocated at Init so the growth branch of `Update` never runs. -/
@[expose] def OrdSolverReachedInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (κ : ℝ) (G : MGraph) (P : ℕ)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) : Prop :=
  OrdSolverReachInv G P model tok ∧ OrdSolverReached cfg κ G model ∧
    model.nextFresh ≤ Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 ∧
    tok.intCap = initTargetCap cfg G

/-- **The representation of the solver.** It is `solverStateRepShift` (the state, the shift
potential, the forward potential and its ghost, and `FwdBoundNat`) together with
`OrdSolverReachedInv` and the two credits `runtimeCredit` and `treeCredit` (with multipliers
`toolMul` and `treeMul`, paying for `toolMul * Δ totalRuntime` and `treeMul * Δ totalTreeUpdates`).
The footprint is that of `solverStateRepShift`. -/
@[expose] noncomputable def solverStateRepFull (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) :
    DSRep (Alg2State cfg) where
  τ := (SolverToken cfg L Rcore × ℕ) × (ℕ × ℕ)
  rep root model tok mem :=
    (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root model tok.1 mem ∧
    OrdSolverReachedInv κ G P model tok.1.1 ∧
    tok.2.1 = runtimeCredit cfg model ∧
    tok.2.2 = treeCredit cfg model
  foot root tok := (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).foot root tok.1
  phi root tok mem :=
    (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).phi root tok.1 mem +
      toolMul * tok.2.1 + treeMul * tok.2.2

/-- `solverStateRepFull` is local, since `OrdSolverReachedInv` and the two credit ghosts do not
read memory and `solverStateRepShift` is local (`solverStateRepShift_local`). -/
theorem solverStateRepFull_local (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ)
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local) :
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).Local := by
  intro b s x mem mem' hag
  obtain ⟨hrep, hphi⟩ := solverStateRepShift_local cfg L P m V psi k epsExp drainUnit unit
    hlocalCore b s x.1 mem mem' hag
  exact ⟨fun h => ⟨hrep h.1, h.2⟩, by simp only [solverStateRepFull, hphi]⟩

/-- The potential of `solverStateRepFull` at a represented state: the potential of
`solverStateRep`, plus `unit` times the unused shift quota, the deposit, and the forward potential
(`solverStateRepShift_phi_eq`), plus `toolMul * runtimeCredit + treeMul * treeCredit`. -/
theorem solverStateRepFull_phi_eq {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {root : ℕ} {model : Alg2State cfg} {tok : (SolverToken cfg L Rcore × ℕ) × (ℕ × ℕ)} {mem : ℕ → ℕ}
    (hrep : (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root model tok.1
      mem)
    (hrc : tok.2.1 = runtimeCredit cfg model)
    (htc : tok.2.2 = treeCredit cfg model) :
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).phi root tok mem =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok.1.1 mem +
        unit * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain +
          chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain) +
        unit * fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain +
        toolMul * runtimeCredit cfg model + treeMul * treeCredit cfg model := by
  dsimp only [solverStateRepFull]
  rw [solverStateRepShift_phi_eq hrep, hrc, htc]

/-- The state that `Init` builds meets the recourse bound: all forward counts are `0`
(`algorithm1_initialize_counts`). -/
theorem fwdBoundNat_init (cfg : Alg2Config) (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ) (Γ : ℕ) :
    FwdBoundNat cfg.P Γ (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain := by
  intro j _
  have h := (algorithm1_initialize_counts cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀
    g₀).2.2.2.2 j
  change (Ordered.algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀
    g₀).1.curFwd j ≤ _
  rw [h]
  exact Nat.zero_le _

/-- The base of the shift quota, `1 ≤ 10 Ψ_game k`, holds since `Ψ_game ≥ 1` and `k ≥ 1`. -/
theorem one_le_ten_psiGame_k (cfg : Alg2Config) :
    1 ≤ 10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ) := by
  have hψ := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
  have hk : (1 : ℝ) ≤ cfg.P.k := by exact_mod_cast cfg.P.hk
  nlinarith

/-- **The potential at Init.** At the state that `Init` builds, with forward ghost `0` and the
initial dual credits `(runtimeCredit, treeCredit)`, the potential of `solverStateRepFull` is at
most that of `solverStateRep` plus `unit · (d + 1) ⌊(10 Ψ_game k)^{d+1}⌋` plus the two initial
credits (`algorithm2_init_potentials`). -/
theorem solverStateRepFull_phi_init_le {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {root : ℕ} {G₀ : MGraph} {g₀ ℓ₀ : ℕ → ℝ} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root
      (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀) tok mem) :
    let s0 := Ordered.algorithm2_init cfg G₀ g₀ ℓ₀
    let tokFull : (SolverToken cfg L Rcore × ℕ) × (ℕ × ℕ) :=
      ((tok, 0), (runtimeCredit cfg s0, treeCredit cfg s0))
    (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root
        s0 (tok, 0) mem ∧
      (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).phi
          root tokFull mem ≤
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem +
          unit * ((cfg.P.d + 1) *
            ⌊(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊) +
          toolMul * runtimeCredit cfg s0 + treeMul * treeCredit cfg s0 := by
  intro s0 tokFull
  obtain ⟨hq, hdep, _, hfwd⟩ := algorithm2_init_potentials cfg G₀ g₀ ℓ₀ (fwdGamma cfg)
    (one_le_ten_psiGame_k cfg)
  have hrepS : (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root
      s0 (tok, 0) mem :=
    ⟨hrep, fwdBoundNat_init cfg G₀ g₀ ℓ₀ _, hfwd.symm⟩
  refine ⟨hrepS, ?_⟩
  rw [solverStateRepFull_phi_eq hrepS rfl rfl, hdep, hfwd]
  simp only [Nat.add_zero, Nat.mul_zero]
  dsimp only [tokFull, s0]
  have h1 := Nat.add_le_add_left (Nat.mul_le_mul_left unit hq)
    ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem)
  omega

end MinCostFlow.MinRatio

end
