module

public import MinCostFlow.MinRatio.ShiftQuotaDeposit
public import MinCostFlow.MinRatio.ShiftForwardPotential
public import MinCostFlow.MinRatio.UpdateAssemblyBase
public import MinCostFlow.MinRatio.UpdateCycleLoopBase
public import MinCostFlow.Chain.Ordered.Algorithm2Facts
import Mathlib.Tactic

/-!
# The shift potential of the min-ratio solver

The shift loop of Update may run many steps in one call. The paper pays for them by
amortization (the game of Lemma 5.11 and the proof of Theorem 7.1, page 29). This file sets up
that amortization on the machine.

* `schedShiftPotential` reads, from the schedule block of the solver in memory, the unused shift
  quota `N = shiftRemainingBudget` and the deposit `chainShiftDeposit` of
  `ShiftQuotaDeposit.lean`, and charges `unit` per unit of each. When `solverStateRep` holds, it
  equals `unit · (N + deposit)` of the model chain (`schedShiftPotential_eq`).
* `solverStateRepShift` is `solverStateRep` with this potential added, and also `unit` times
  the forward potential `fwdPotential` of `ShiftForwardPotential.lean`, kept as a ghost in the
  token. Its representation also asks for the recourse invariant `FwdBoundNat` with
  `Γ = fwdGamma cfg = ⌈γ_r(M₀²)⌉`. It is local (`solverStateRepShift_local`).
* `update_shift_amortized` turns the cost clause of `solverOps_update_runs`, which charges the
  loop by its actual number of steps, into an amortized bound against the shift potential. One
  call then costs the budget without the loop term, plus one loop step, plus `unit ·
  shiftDeposit 0` per update of the batch, plus `unit · shiftDeposit i` per update forwarded to
  each deeper level `0 < i < d`.
* `update_fwd_amortized` pays the last charge with the forward potential. The paper bounds it
  by the recourse of the sparse cores ("the number of updates received at level `i` is bounded
  by `γ_r^i Q`", page 29). One call then costs the budget without the loop term, plus one loop
  step, plus `unit · W_0` per update of the batch, with `W_0 = fwdWeight … 0`. This needs the
  recourse invariant on the pre-loop chain, which comes from the chain invariant
  (`fwdBoundNat_of_chainRecBound`). `fwdWeight_le_timeFactor` (`ShiftForwardWeightBound.lean`)
  shows `W_0 = m^{o(1)}`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- The unused shift quota, read from the schedule block at `levelsEnd`: shift counts at
`levelsEnd + (d + 1) + j` and rebuild counts at `levelsEnd + 2 (d + 1) + j`. -/
@[expose] noncomputable def schedQuota (cfg : Alg2Config) (mem : ℕ → ℕ) (levelsEnd : ℕ) : ℕ :=
  ∑ j : Fin (cfg.P.d + 1),
    (⌊gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
        (fun i => mem (levelsEnd + 2 * (cfg.P.d + 1) + i)) j.val⌋₊ -
      mem (levelsEnd + (cfg.P.d + 1) + j.val))

/-- The deposit, read from the update counts at `levelsEnd + 3 (d + 1) + i`. -/
@[expose] noncomputable def schedDeposit (cfg : Alg2Config) (mem : ℕ → ℕ) (levelsEnd : ℕ) : ℕ :=
  ∑ i ∈ Finset.range cfg.P.d,
    shiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) i *
      mem (levelsEnd + 3 * (cfg.P.d + 1) + i)

/-- The shift potential: `unit` per unit of unused quota and of deposit, when the schedule block
is owned by the token (and `0` otherwise, so that the potential reads only owned cells). -/
@[expose] noncomputable def schedShiftPotential (cfg : Alg2Config) (unit levelsEnd : ℕ) (owned : ℕ → Prop)
    (mem : ℕ → ℕ) : ℕ :=
  open Classical in
  if ∀ j < 4 * (cfg.P.d + 1) + 1, owned (levelsEnd + j) then
    unit * (schedQuota cfg mem levelsEnd + schedDeposit cfg mem levelsEnd)
  else 0

private theorem gameShiftBound_congr (P : ChainParams) (psi : ℝ) {r r' : ℕ → ℕ} (j : ℕ)
    (h : ∀ i ≤ j, r' i = r i) : gameShiftBound P psi r' j = gameShiftBound P psi r j := by
  unfold gameShiftBound
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- When the schedule block holds the counts of the model chain, the potential is `unit` times
the unused quota plus the deposit of the chain. -/
theorem schedShiftPotential_eq {cfg : Alg2Config} {unit levelsEnd : ℕ} {owned : ℕ → Prop}
    {mem : ℕ → ℕ} {model : Alg2State cfg} (hsched : SolverScheduleAt mem levelsEnd model)
    (hown : ∀ j < 4 * (cfg.P.d + 1) + 1, owned (levelsEnd + j)) :
    schedShiftPotential cfg unit levelsEnd owned mem =
      unit * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain +
        chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain) := by
  obtain ⟨_, hs, hr, hu, _⟩ := hsched
  unfold schedShiftPotential
  rw [ite_eq_left hown]
  congr 2
  · unfold schedQuota shiftRemainingBudget
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs j.val (Nat.lt_succ_iff.mp j.isLt), gameShiftBound_congr _ _ j.val
      (fun i hi => hr i (le_trans hi (Nat.lt_succ_iff.mp j.isLt)))]
  · unfold schedDeposit chainShiftDeposit
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hu i (le_of_lt (Finset.mem_range.mp hi))]

/-- The integer recourse factor `Γ = ⌈γ_r(M₀²)⌉` of the forward potential. -/
@[expose] noncomputable def fwdGamma (cfg : Alg2Config) : ℕ := ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊

/-- `solverStateRep` with two potentials added: the shift potential `schedShiftPotential`, read
from memory, and `unit` times the forward potential `fwdPotential` of `ShiftForwardPotential.lean`.
The forward potential depends on `curFwd`, which memory does not hold, so the token carries it as
a second, ghost component. The representation asks that this ghost equal the forward potential
of the model chain, and that the chain meet the recourse invariant `FwdBoundNat` with
`Γ = fwdGamma cfg` (the first half of `ChainRecBound`, which `ChainInv.hRecFwd` gives). The
footprint is that of `solverStateRep`. -/
@[expose] noncomputable def solverStateRepShift (cfg : Alg2Config)
    (L P m V psi k epsExp drainUnit unit : ℕ) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) :
    DSRep (Alg2State cfg) where
  τ := SolverToken cfg L Rcore × ℕ
  rep root model tok mem := (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model
      tok.1 mem ∧ FwdBoundNat cfg.P (fwdGamma cfg) model.chain ∧
    tok.2 = fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain
  foot root tok := (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok.1
  phi root tok mem := (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok.1 mem +
    schedShiftPotential cfg unit tok.1.levelsEnd tok.1.owned mem + unit * tok.2

/-- `solverStateRepShift` is local whenever `Rcore` is, since the shift potential reads only
cells that the token owns. -/
theorem solverStateRepShift_local (cfg : Alg2Config) (L P m V psi k epsExp drainUnit unit : ℕ)
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local) :
    (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).Local := by
  intro root model tok mem₁ mem₂ hag
  have hbase := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore root model tok.1
    mem₁ mem₂ hag
  refine ⟨fun h => ⟨hbase.1 h.1, h.2⟩, ?_⟩
  change _ + _ + _ = _ + _ + _
  rw [hbase.2]
  congr 2
  unfold schedShiftPotential
  split_ifs with hown
  · have hcell : ∀ j < 4 * (cfg.P.d + 1) + 1, mem₁ (tok.1.levelsEnd + j) = mem₂ (tok.1.levelsEnd + j) :=
      fun j hj => hag _ (Or.inl (hown j hj))
    have h2 : ∀ i ≤ cfg.P.d, mem₁ (tok.1.levelsEnd + 2 * (cfg.P.d + 1) + i) =
        mem₂ (tok.1.levelsEnd + 2 * (cfg.P.d + 1) + i) := fun i hi => by
      rw [Nat.add_assoc]; exact hcell _ (by omega)
    have h1 : ∀ i ≤ cfg.P.d, mem₁ (tok.1.levelsEnd + (cfg.P.d + 1) + i) =
        mem₂ (tok.1.levelsEnd + (cfg.P.d + 1) + i) := fun i hi => by
      rw [Nat.add_assoc]; exact hcell _ (by omega)
    have h3 : ∀ i < cfg.P.d, mem₁ (tok.1.levelsEnd + 3 * (cfg.P.d + 1) + i) =
        mem₂ (tok.1.levelsEnd + 3 * (cfg.P.d + 1) + i) := fun i hi => by
      rw [Nat.add_assoc]; exact hcell _ (by omega)
    congr 2
    · unfold schedQuota
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h1 j.val (Nat.lt_succ_iff.mp j.isLt), gameShiftBound_congr _ _ j.val
        (fun i hi => (h2 i (le_trans hi (Nat.lt_succ_iff.mp j.isLt))).symm)]
    · unfold schedDeposit
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [h3 i (Finset.mem_range.mp hi)]
  · rfl

/-- The potential of `solverStateRepShift` at a represented state. -/
theorem solverStateRepShift_phi_eq {cfg : Alg2Config} {L P m V psi k epsExp drainUnit unit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore × ℕ} {mem : ℕ → ℕ}
    (hrep : (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root model tok
      mem) :
    (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).phi root tok mem =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok.1 mem +
        unit * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain +
          chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain) +
        unit * fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain := by
  obtain ⟨hbase, _, hghost⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, _, hsched, _, _, _, _, _, _, _, _, _, _, htags⟩ := hbase
  obtain ⟨hOwn, _, _, _, _, t5, _⟩ := htags
  change _ + _ + _ = _
  rw [schedShiftPotential_eq hsched (fun j hj => hOwn _ (by rw [t5 j hj]; decide)), hghost]

/-- A state of `solverStateRep` that meets the recourse invariant is a state of
`solverStateRepShift`, with the forward potential of the chain as the ghost. -/
theorem solverStateRepShift_of_rep {cfg : Alg2Config} {L P m V psi k epsExp drainUnit unit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hfwd : FwdBoundNat cfg.P (fwdGamma cfg) model.chain) :
    (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root model
      (tok, fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain) mem :=
  ⟨hrep, hfwd, rfl⟩

/-! ## The amortized cost of Update -/

/-- The shift loop of Algorithm 2 keeps the cumulative update counts. -/
theorem algorithm2_loopWith_recUpdates (cfg : Alg2Config) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) :
    ∀ (B : ℕ) (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
      (lctOps : ℕ),
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ B →
      (Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).1.recUpdates =
        ch.recUpdates := by
  intro B
  induction B with
  | zero =>
    intro ch branD passes lctOps hB
    rw [Ordered.algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · rfl
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => rfl
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap; omega
        · simp [hCap]
  | succ B ihB =>
    intro ch branD passes lctOps hB
    rw [Ordered.algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · rfl
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => rfl
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left_of_eq_true (eq_true hCap)]
          have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          rw [ihB (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 _ _ _ (by omega)]
          dsimp only [Ordered.algorithm1_shift]
          split_ifs <;> rfl
        · rw [dite_eq_right_of_eq_false (eq_false hCap)]

/-- The chain after an `Update` of the model is the chain after the shift loop that starts from
the pre-loop state. -/
theorem algorithm2_update_chain (cfg : Alg2Config) (κ : ℝ) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) (actual : ℝ) :
    ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain =
      (let model1 := alg2PreLoopState cfg model U gVec lVec
       Chain.Ordered.algorithm2_loopWith cfg κ model1.extG model1.extToInt model1.extg
        model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps).1 := by
  change (Chain.Ordered.algorithm2_updateWith cfg κ model U gVec lVec actual).1.chain = _
  obtain ⟨hnone, hsome⟩ := Chain.Ordered.algorithm2_updateWith_eq_of_loop κ model U gVec lVec actual
  revert hnone hsome
  dsimp only
  generalize hopt : (Chain.Ordered.algorithm2_loopWith cfg κ _ _ _ _ _ _ _ _).2.2.2.2 = opt
  intro hnone hsome
  cases opt with
  | none => rw [hnone rfl]; rfl
  | some Δ => rw [hsome Δ rfl]; rfl

private theorem translateBatch_length (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) :
    ∀ U : List Update, (translateBatch curExt e2i i2e nf U).2.2.2.2.length = U.length
  | [] => rfl
  | u :: rest => by
    simp [translateBatch, translateBatch_length _ _ _ _ rest]

/-- **Amortized cost of Update against the shift potential.** Let `cost + φ' + N' · B ≤ R + (N₁
+ 1) · B + φ` be the cost clause of `solverOps_update_runs`, where `N₁` is the unused quota of
the pre-loop chain, `N'` that of the final chain, and `B` the cost of one loop step. Then, with
the potential `B · (N + deposit)` added on both sides, one call costs `R + B` plus `B ·
shiftDeposit 0` per update of the batch (when `d > 0`), plus `B · shiftDeposit i` per update
forwarded to each level `0 < i < d` (the growth of `deeperDeposit`). -/
theorem update_shift_amortized (cfg : Alg2Config) (κ : ℝ) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) (actual : ℝ) {cost phi phi' R B : ℕ}
    (h : cost + phi' +
        shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
          ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain * B ≤
      R + (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
        (alg2PreLoopState cfg model U gVec lVec).chain + 1) * B + phi) :
    let ψ := alg2PsiGame cfg.Ψ cfg.P.M₀
    let ch' := ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain
    cost + (phi' + B * (shiftRemainingBudget cfg.P ψ ch' + chainShiftDeposit cfg.P cfg.N₀ ψ ch')) +
        B * deeperDeposit cfg.P cfg.N₀ ψ 0 model.chain ≤
      R + B + B * (if 0 < cfg.P.d then shiftDeposit cfg.P cfg.N₀ ψ 0 * U.length else 0) +
        B * deeperDeposit cfg.P cfg.N₀ ψ 0 ch' +
        (phi + B * (shiftRemainingBudget cfg.P ψ model.chain +
          chainShiftDeposit cfg.P cfg.N₀ ψ model.chain)) := by
  intro ψ ch'
  let model1 := alg2PreLoopState cfg model U gVec lVec
  have hψ : 0 ≤ ψ := le_trans zero_le_one (alg2PsiGame_ge_one _ _)
  -- the pre-loop chain is one step of Algorithm 1's `Update` on the translated batch
  have hdep := algorithm1_update_quota_deposit cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
    (fun e' => gVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
    (fun e' => lVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
    hψ
  rw [translateBatch_length] at hdep
  change shiftRemainingBudget cfg.P ψ model1.chain + chainShiftDeposit cfg.P cfg.N₀ ψ model1.chain +
      deeperDeposit cfg.P cfg.N₀ ψ 0 model.chain ≤ _ + _ + _ + deeperDeposit cfg.P cfg.N₀ ψ 0 model1.chain
    at hdep
  -- the loop keeps the cumulative counts and does not raise the deposit
  have hch' : ch' = (Chain.Ordered.algorithm2_loopWith cfg κ model1.extG model1.extToInt model1.extg
      model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps).1 :=
    algorithm2_update_chain cfg κ model U gVec lVec actual
  have hrec : ch'.recUpdates = model1.chain.recUpdates := by
    rw [hch']; exact algorithm2_loopWith_recUpdates cfg κ _ _ _ _ _ _ _ _ _ le_rfl
  have hupd : ∀ j, ch'.updCount j ≤ model1.chain.updCount j := by
    rw [hch']; exact (algorithm2_loopWith_updCount_le cfg κ _ _ _ _ _ _ _ _ _ le_rfl).2
  have hdeep : deeperDeposit cfg.P cfg.N₀ ψ 0 ch' = deeperDeposit cfg.P cfg.N₀ ψ 0 model1.chain := by
    unfold deeperDeposit; rw [hrec]
  have hdepLe : chainShiftDeposit cfg.P cfg.N₀ ψ ch' ≤ chainShiftDeposit cfg.P cfg.N₀ ψ model1.chain :=
    Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hupd i)
  rw [hdeep]
  have h' : cost + phi' + shiftRemainingBudget cfg.P ψ ch' * B ≤
      R + (shiftRemainingBudget cfg.P ψ model1.chain + 1) * B + phi := h
  clear h
  have hmul := Nat.mul_le_mul_left B (Nat.add_le_add_left hdepLe (shiftRemainingBudget cfg.P ψ ch'))
  have hdepB := Nat.mul_le_mul_left B hdep
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at hmul hdepB h' ⊢
  rw [Nat.mul_comm B (shiftRemainingBudget cfg.P ψ ch'),
    Nat.mul_comm B (shiftRemainingBudget cfg.P ψ model1.chain)] at *
  omega

/-- The recourse bound of the chain invariant (`ChainInv.hRecFwd`) gives `FwdBoundNat` with
`Γ = fwdGamma cfg`. -/
theorem fwdBoundNat_of_chainRecBound {cfg : Alg2Config} {ch : ChainState cfg.T cfg.P}
    (h : ChainRecBound cfg.P (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ch) :
    FwdBoundNat cfg.P (fwdGamma cfg) ch :=
  fwdBoundNat_of_real fun j hj => (h j hj).1

/-- **Amortized cost of Update against both potentials.** Take the cost clause `h` of
`update_shift_amortized`. Assume the recourse invariant `FwdBoundNat` holds on the chain before
the call and on the pre-loop chain (the chain after Algorithm 1's `Update`). Then, with `B` times
the shift potential and `B` times the forward potential added on both sides, one call costs
`R + B` plus `B · W_0` per update of the batch, where `W_0 = fwdWeight … 0`. The invariant also
holds after the call, since the shift loop keeps it (`algorithm2_loopWith_fwd`).

The proof adds three facts: `update_shift_amortized`, which leaves the growth of
`deeperDeposit 0` to pay; `algorithm1_update_fwd`, which pays it with the forward potential at
`Γ W_1` per update; and `algorithm2_loopWith_fwd`, by which the loop does not raise the forward
potential. Then `shiftDeposit 0 + Γ W_1 = W_0` (`fwdWeight_succ`). -/
theorem update_fwd_amortized (cfg : Alg2Config) (κ : ℝ) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) (actual : ℝ) {cost phi phi' R B : ℕ}
    (h : cost + phi' +
        shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
          ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain * B ≤
      R + (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
        (alg2PreLoopState cfg model U gVec lVec).chain + 1) * B + phi)
    (hBefore : FwdBoundNat cfg.P (fwdGamma cfg) model.chain)
    (hPre : FwdBoundNat cfg.P (fwdGamma cfg) (alg2PreLoopState cfg model U gVec lVec).chain) :
    let ψ := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Γ := fwdGamma cfg
    let ch' := ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain
    cost + (phi' + B * (shiftRemainingBudget cfg.P ψ ch' + chainShiftDeposit cfg.P cfg.N₀ ψ ch') +
        B * fwdPotential cfg.P cfg.N₀ ψ Γ ch') ≤
      R + B + B * fwdWeight cfg.P cfg.N₀ ψ Γ 0 * U.length +
        (phi + B * (shiftRemainingBudget cfg.P ψ model.chain +
          chainShiftDeposit cfg.P cfg.N₀ ψ model.chain) +
          B * fwdPotential cfg.P cfg.N₀ ψ Γ model.chain) ∧
      FwdBoundNat cfg.P Γ ch' := by
  intro ψ Γ ch'
  let model1 := alg2PreLoopState cfg model U gVec lVec
  have hA : cost + (phi' + B * (shiftRemainingBudget cfg.P ψ ch' +
        chainShiftDeposit cfg.P cfg.N₀ ψ ch')) + B * deeperDeposit cfg.P cfg.N₀ ψ 0 model.chain ≤
      R + B + B * (if 0 < cfg.P.d then shiftDeposit cfg.P cfg.N₀ ψ 0 * U.length else 0) +
        B * deeperDeposit cfg.P cfg.N₀ ψ 0 ch' +
        (phi + B * (shiftRemainingBudget cfg.P ψ model.chain +
          chainShiftDeposit cfg.P cfg.N₀ ψ model.chain)) :=
    update_shift_amortized cfg κ model U gVec lVec actual h
  have hch' : ch' = (Chain.Ordered.algorithm2_loopWith cfg κ model1.extG model1.extToInt model1.extg
      model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps).1 :=
    algorithm2_update_chain cfg κ model U gVec lVec actual
  obtain ⟨hloopP, hloopB⟩ := algorithm2_loopWith_fwd cfg κ model1.extG model1.extToInt model1.extg
    model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps ψ Γ
  -- the pre-loop chain is one step of Algorithm 1's `Update` on the translated batch
  have hfwd := algorithm1_update_fwd cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
    (fun e' => gVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
    (fun e' => lVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
    ψ Γ hBefore hPre
  rw [translateBatch_length] at hfwd
  change fwdPotential cfg.P cfg.N₀ ψ Γ model1.chain + deeperDeposit cfg.P cfg.N₀ ψ 0 model1.chain ≤
      fwdPotential cfg.P cfg.N₀ ψ Γ model.chain + deeperDeposit cfg.P cfg.N₀ ψ 0 model.chain +
        Γ * fwdWeight cfg.P cfg.N₀ ψ Γ 1 * U.length at hfwd
  -- the loop keeps the cumulative counts and does not raise the forward potential
  have hrec : ch'.recUpdates = model1.chain.recUpdates := by
    rw [hch']; exact algorithm2_loopWith_recUpdates cfg κ _ _ _ _ _ _ _ _ _ le_rfl
  have hdeep : deeperDeposit cfg.P cfg.N₀ ψ 0 ch' = deeperDeposit cfg.P cfg.N₀ ψ 0 model1.chain := by
    unfold deeperDeposit; rw [hrec]
  have hP' : fwdPotential cfg.P cfg.N₀ ψ Γ ch' ≤ fwdPotential cfg.P cfg.N₀ ψ Γ model1.chain := by
    rw [hch']; exact hloopP
  refine ⟨?_, by rw [hch']; exact hloopB hPre⟩
  have hW : (if 0 < cfg.P.d then shiftDeposit cfg.P cfg.N₀ ψ 0 * U.length else 0) +
      Γ * fwdWeight cfg.P cfg.N₀ ψ Γ 1 * U.length = fwdWeight cfg.P cfg.N₀ ψ Γ 0 * U.length := by
    split_ifs with hd
    · rw [fwdWeight_succ cfg.P cfg.N₀ ψ Γ hd]; ring
    · rw [fwdWeight_of_le cfg.P cfg.N₀ ψ Γ (by omega : cfg.P.d ≤ 1),
        fwdWeight_of_le cfg.P cfg.N₀ ψ Γ (by omega : cfg.P.d ≤ 0)]
      ring
  rw [hdeep] at hA
  have hfB := Nat.mul_le_mul_left B hfwd
  have hPB := Nat.mul_le_mul_left B hP'
  have hWB := congrArg (B * ·) hW
  simp only [Nat.mul_add] at hfB hWB
  rw [← Nat.mul_assoc B (fwdWeight cfg.P cfg.N₀ ψ Γ 0)] at hWB
  generalize B * (if 0 < cfg.P.d then shiftDeposit cfg.P cfg.N₀ ψ 0 * U.length else 0) = S0
    at hA hWB
  generalize B * (Γ * fwdWeight cfg.P cfg.N₀ ψ Γ 1 * U.length) = G1 at hfB hWB
  generalize B * fwdWeight cfg.P cfg.N₀ ψ Γ 0 * U.length = W0 at hWB ⊢
  omega

end MinCostFlow.MinRatio
