module

public import MinCostFlow.MinRatio.UpdateCycleLoopBase
public import MinCostFlow.SparseCore.Program.AssemblyContract

/-!
# Shared facts for the corrected inner specs of the solver

The corrected inner specs (`WireFindCycle.lean`, `WireInitSpec.lean`, `WireChainSpecs.lean`)
use three things that the existing specs of `MinRatio/` do not have.

* `OffTreeRecBound`: the gradient and the length stored in every off-tree edge record are at
  most `B` in absolute value. `OffTreeRecInv` bounds only the detector. The evaluation of a
  cycle (Algorithm 2, page 29) sums these values, so the sum must fit in `L` limbs.
* `WireCapFacts`: the cap and limb conditions of the sparse-core contract
  (`SparseCoreCapHyp`, in `sparseCoreOrdMachineContractK` and so in
  `sparseCoreOrdMachineContractKFBL`) hold at every level `i < d` of the chain,
  with the level's size bounds `(lvlM i, N₀)`, for every pair of caps whose sum plus two is at
  most `capLimit`. A program that calls the sparse-core module at level `i` with such caps may
  use the contract there.
* `wire_credit_step`: the arithmetic step that turns a cost of the form "fixed part plus `mul`
  times the rise of the chain's cumulative runtime" into a fixed amortized cost, once a credit
  `mul * (cap - runtime)` is added to the potential.

The transport lemma `offTreeRecBound_of_agree` moves `OffTreeRecBound` across memories that
agree on the record pointers and the record blocks, as `offTreeRecInv_of_agree` does for
`OffTreeRecInv`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain SparseCore.Program

/-- The gradient, length, and flow of every off-tree edge record are at most `B` in absolute value.
Together with `OffTreeRecInv` (which bounds the detector), this gives the full four-field bound
needed both for cycle evaluation and for linking an off-tree edge back into the path tree. -/
@[expose] def OffTreeRecBound {cfg : Alg2Config} (model : Alg2State cfg) (L : ℕ)
    (mem : ℕ → ℕ) (edgeRecords : ℕ) (B : ℤ) : Prop :=
  ∀ e ∈ model.extG.E, model.extToInt e ∉ model.chain.toTreeChain.chainTree.E →
    ∀ val, PathEdgeAt mem (mem (edgeRecords + model.extToInt e)) 4 L (some val) →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B

/-- The cap and limb conditions of the sparse-core contract at every level `i < d` of the
chain, with the size bounds `(lvlM i, N₀)` that the model passes to the tool at level `i`, for
all caps `vCap`, `eCap` with `vCap + eCap + 2 ≤ capLimit`. -/
@[expose] def WireCapFacts {cfg : Alg2Config} (capExp limbMul L capLimit : ℕ)
    (model : Alg2State cfg) : Prop :=
  ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
    SparseCoreCapHyp capExp limbMul L (model.chain.lvlM i) model.chain.N₀ vCap eCap

/-- `WireCapFacts` holds when `capLimit` is at most `(lvlM i + N₀ + 2) ^ capExp` and the limb count
is at most `limbMul · (⌊log₂ (lvlM i + N₀ + 2)⌋ + 1)` at every level. -/
theorem wireCapFacts_of_le {cfg : Alg2Config} {capExp limbMul L capLimit : ℕ}
    {model : Alg2State cfg}
    (h : ∀ i < cfg.P.d,
      capLimit ≤ (model.chain.lvlM i + model.chain.N₀ + 2) ^ capExp ∧
      L ≤ limbMul * (Nat.log 2 (model.chain.lvlM i + model.chain.N₀ + 2) + 1)) :
    WireCapFacts capExp limbMul L capLimit model := by
  intro i hi vCap eCap hcap
  refine ⟨hcap.trans (h i hi).1, (h i hi).2.trans (Nat.mul_le_mul_left _ ?_)⟩
  unfold SparseCore.bundleLogFactor
  have h1 : 1 ≤ Nat.log 2 (model.chain.lvlM i + model.chain.N₀ + 2) + 1 := by omega
  calc Nat.log 2 (model.chain.lvlM i + model.chain.N₀ + 2) + 1
      = (Nat.log 2 (model.chain.lvlM i + model.chain.N₀ + 2) + 1) ^ 1 := (pow_one _).symm
    _ ≤ (Nat.log 2 (model.chain.lvlM i + model.chain.N₀ + 2) + 1) ^ 2 :=
        Nat.pow_le_pow_right h1 (by decide)

/-- `WireCapFacts` depends on the model only through the level size bounds `lvlM` and `N₀`. -/
theorem WireCapFacts.congr {cfg : Alg2Config} {capExp limbMul L capLimit : ℕ}
    {model model' : Alg2State cfg} (h : WireCapFacts capExp limbMul L capLimit model)
    (hM : ∀ i < cfg.P.d, model'.chain.lvlM i = model.chain.lvlM i)
    (hN : model'.chain.N₀ = model.chain.N₀) :
    WireCapFacts capExp limbMul L capLimit model' := by
  intro i hi vCap eCap hcap
  rw [hM i hi, hN]
  exact h i hi vCap eCap hcap

/-- Transport `OffTreeRecBound` across memories that agree on the tag-13 pointers and the tag-18
record blocks. -/
theorem offTreeRecBound_of_agree {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {root : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem₁ mem₂ : ℕ → ℕ} {B : ℤ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₁)
    (hBd : OffTreeRecBound model L mem₁ tok.edgeRecords B)
    (hag : ∀ a, (tok.tag a = 13 ∨ tok.tag a = 18) → mem₂ a = mem₁ a) :
    OffTreeRecBound model L mem₂ tok.edgeRecords B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hedgeAcc, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, t13, _, _, _, t1718, _⟩ := htags
  intro e he hnot val hpa
  have hptr : mem₂ (tok.edgeRecords + model.extToInt e) =
      mem₁ (tok.edgeRecords + model.extToInt e) :=
    hag _ (Or.inl (t13 _ (hedgeAcc.1 e he).1))
  rw [hptr] at hpa
  exact hBd e he hnot val (hpa.congr fun x hx1 hx2 => by
    have hx : x = mem₁ (tok.edgeRecords + model.extToInt e) +
        (x - mem₁ (tok.edgeRecords + model.extToInt e)) := by omega
    rw [hx]; exact (hag _ (Or.inr ((t1718 e he).2 hnot _ (by omega)))).symm)

/-- **The credit step.** If a step costs at most `fixed` plus `mul` times the rise `T' - T` of a
cumulative count (here the chain's `totalRuntime`), the count does not fall, and it stays below
`cap`, then adding the credit `mul * (cap - T)` to the potential makes the cost of the step at
most `fixed`. -/
theorem wire_credit_step {cost phi phi' fixed mul T T' cap : ℕ}
    (hcost : cost + phi' ≤ fixed + mul * (T' - T) + phi) (hmono : T ≤ T') (hcap : T' ≤ cap) :
    cost + (phi' + mul * (cap - T')) ≤ fixed + (phi + mul * (cap - T)) := by
  have hsplit : mul * (cap - T) = mul * (T' - T) + mul * (cap - T') := by
    rw [← Nat.mul_add]; congr 1; omega
  rw [hsplit]
  omega

end MinCostFlow.MinRatio
