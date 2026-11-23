module

public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.DetectorThreshold
public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.IPM.Machine.MinRatioContract
import Mathlib.Tactic

/-!
# The tree budget between operations (`SolverTreeBudgetInv`)

Each good cycle of `Update` raises the tree budget by `X = maxPaths · 2^(3E + 2 + P)`, and no
operation lowers it. So the budget that holds between operations grows with the number of
`Update`s. This file defines that budget and proves the facts that the operations use.

1. **The counter.** `Alg2State.updateCount` counts the `Update`s. A state reached by a history of
   `T` stages has `updateCount ≤ T` (`ordAlg2_minRatioState_updateCount_le`). So the state passed
   to `Update` has `updateCount ≤ 2 G.m` (`ordAlg2_detected_updateCount_le`).
2. **The invariant** `SolverTreeBudgetInv`. The tree holds `PathTreeNumericInv` at
   `B₀ + updateCount · X` and `updateCount · X`, with `B₀ = 2^(P + 2E + 2)`. Besides, the stored
   gradients and lengths are in range, the accumulators are not negative, and the record blocks of
   two live off-tree edges are apart (`OffTreeRecSep`, the second half of `OffTreeRecInv`).
3. **The records at the start of `Update`.** Given the rep, the value of each off-tree record is
   fixed by the model. So the first half of `OffTreeRecInv` and all of `OffTreeRecBound` hold at
   every `B ≥ B₀`, when the flows are at most `2^E` and every accumulator is below its threshold
   (`offTreeRec_of_model`). These facts hold at every `Update`: the flow bound is in its `pre`,
   and the accumulator bound holds after every `Detect`.
4. **The fit.** With `updateCount ≤ 2 G.m + 1`, the budget fits whenever
   `B₀ + 2 G.m X ≤ B_bound`, `2 G.m X ≤ R_bound` and the fit at `B_bound + X`, `R_bound + X`
   hold (`treeBudget_fit`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program

/-! ## 1. The counter -/

/-- `Update` adds one to the counter, in both branches. -/
theorem ordAlg2_updateWith_updateCount (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U : List Update) (g l : ℕ → ℝ) (η : ℝ) :
    (Chain.Ordered.algorithm2_updateWith cfg κ st U g l η).1.updateCount = st.updateCount + 1 := by
  dsimp only [Chain.Ordered.algorithm2_updateWith]
  split <;> rfl

/-- `Detect` keeps the counter. -/
theorem algorithm2_detect_updateCount (cfg : Alg2Config) (st : Alg2State cfg) :
    (algorithm2_detect cfg st).2.updateCount = st.updateCount :=
  rfl

/-- A state reached by a history of `T` stages has `updateCount ≤ T`: Init sets it to `0`, each
`Update` stage adds one, and each `Detect` stage keeps it. -/
theorem ordAlg2_minRatioState_updateCount_le (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) :
    ∀ T, (minRatioState (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).eraseFailure
      D η op T).updateCount ≤ T
  | 0 => Nat.le_of_eq rfl
  | T + 1 => by
    have ih := ordAlg2_minRatioState_updateCount_le cfg κ D η op T
    simp only [minRatioState]
    split
    · have h := ordAlg2_updateWith_updateCount cfg κ
        (minRatioState (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).eraseFailure D η op T)
        (D.U (T + 1)) (D.g (T + 1)) (D.ℓ (T + 1)) (η (T + 1))
      exact le_of_eq_of_le h (by omega)
    · exact ih.trans (Nat.le_succ T)

/-- The state passed to `Update` has `updateCount ≤ 2 G.m`: it is the `Detect` output of a state
reached in at most `2 G.m` stages (`MinRatioDetectedWith.stages_le`). -/
theorem ordAlg2_detected_updateCount_le {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {s : Alg2State cfg} {changed : ℕ → Prop} {g l : ℕ → ℝ}
    (h : MinRatioDetectedWith (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G s changed g l) :
    s.updateCount ≤ 2 * G.m := by
  obtain ⟨D, η, op, T, _, _, hs, hT⟩ := h.stages_le
  subst hs
  exact (ordAlg2_minRatioState_updateCount_le cfg κ D η op T).trans hT

/-! ## 2. The invariant -/

/-- The second half of `OffTreeRecInv`: the record blocks of two live off-tree edges are
`2 + 4 L` apart. It reads only the record pointers. -/
@[expose] def OffTreeRecSep {cfg : Alg2Config} (model : Alg2State cfg) (L : ℕ)
    (mem : ℕ → ℕ) (edgeRecords : ℕ) : Prop :=
  ∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E, e₁ ≠ e₂ →
    model.extToInt e₁ ∉ model.chain.toTreeChain.chainTree.E →
    model.extToInt e₂ ∉ model.chain.toTreeChain.chainTree.E →
    mem (edgeRecords + model.extToInt e₁) + (2 + 4 * L) ≤ mem (edgeRecords + model.extToInt e₂) ∨
    mem (edgeRecords + model.extToInt e₂) + (2 + 4 * L) ≤ mem (edgeRecords + model.extToInt e₁)

/-- The second half of `OffTreeRecInv` is `OffTreeRecSep`. -/
theorem OffTreeRecInv.sep {cfg : Alg2Config} {model : Alg2State cfg} {L : ℕ} {mem : ℕ → ℕ}
    {edgeRecords : ℕ} {B : ℤ} (h : OffTreeRecInv model L mem edgeRecords B) :
    OffTreeRecSep model L mem edgeRecords :=
  h.2

/-- `OffTreeRecSep` moves to a memory that keeps the record pointers of the live edges. -/
theorem OffTreeRecSep.of_agree {cfg : Alg2Config} {model : Alg2State cfg} {L : ℕ}
    {mem mem' : ℕ → ℕ} {edgeRecords : ℕ} (h : OffTreeRecSep model L mem edgeRecords)
    (hag : ∀ e ∈ model.extG.E, mem' (edgeRecords + model.extToInt e) =
      mem (edgeRecords + model.extToInt e)) :
    OffTreeRecSep model L mem' edgeRecords := by
  intro e₁ he₁ e₂ he₂ hne hn₁ hn₂
  rw [hag e₁ he₁, hag e₂ he₂]
  exact h e₁ he₁ e₂ he₂ hne hn₁ hn₂

/-- The record pointer of a live edge lies in the foot of the rep: it has tag `13`. -/
theorem solverStateRep_recPtr_foot {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    {e : ℕ} (he : e ∈ model.extG.E) :
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok
      (tok.edgeRecords + model.extToInt e) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hedgeAcc, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, _, _, _, _, t13, _⟩ := htags
  exact Or.inl (hOwn _ (by rw [t13 _ (hedgeAcc.1 e he).1]; decide))

/-- The record pointer of a live edge has tag `13`. -/
theorem solverStateRep_recPtr_tag {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    {e : ℕ} (he : e ∈ model.extG.E) : tok.tag (tok.edgeRecords + model.extToInt e) = 13 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hedgeAcc, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, t13, _⟩ := htags
  exact t13 _ (hedgeAcc.1 e he).1

/-- A cell of the foot of core `i` has tag `21 + i`. -/
theorem solverStateRep_core_tag {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    {i a : ℕ} (hi : i < cfg.P.d) (ha : Rcore.foot (tok.coreHandle i) (tok.coreTok i) a) :
    tok.tag a = 21 + i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcore⟩ := htags
  exact hcore i hi a ha

/-- The internal index of a live edge is below the capacity of the internal tables. -/
theorem solverStateRep_extToInt_lt {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    {e : ℕ} (he : e ∈ model.extG.E) : model.extToInt e < tok.intCap := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hedgeAcc, _⟩ := hrep
  exact (hedgeAcc.1 e he).1

/-- `OffTreeRecSep` moves to a new table of record pointers that holds the same pointers at the
live edges. -/
theorem OffTreeRecSep.of_copy {cfg : Alg2Config} {model : Alg2State cfg} {L : ℕ}
    {mem mem' : ℕ → ℕ} {edgeRecords edgeRecords' : ℕ} (h : OffTreeRecSep model L mem edgeRecords)
    (hag : ∀ e ∈ model.extG.E, mem' (edgeRecords' + model.extToInt e) =
      mem (edgeRecords + model.extToInt e)) :
    OffTreeRecSep model L mem' edgeRecords' := by
  intro e₁ he₁ e₂ he₂ hne hn₁ hn₂
  rw [hag e₁ he₁, hag e₂ he₂]
  exact h e₁ he₁ e₂ he₂ hne hn₁ hn₂

/-- The budget base `B₀ = 2^(P + 2E + 2)`. -/
@[expose] def treeBudgetBase (P E : ℕ) : ℤ := (2 : ℤ) ^ (P + 2 * E + 2)

/-- **The tree budget between operations.** `X` is the raise of one good cycle. -/
@[expose] def SolverTreeBudgetInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (G : MGraph) (P E : ℕ) (X : ℤ)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) : Prop :=
  model.updateCount ≤ 2 * G.m + 1 ∧
  (∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ E ∧
    (2 : ℝ) ^ (-(E : ℤ)) ≤ model.extℓ e ∧ model.extℓ e ≤ (2 : ℝ) ^ E) ∧
  (∀ e, 0 ≤ model.detectAccum e) ∧
  OffTreeRecSep model L mem tok.edgeRecords ∧
  PathTreeNumericInv tok.tree tok.trees (treeBudgetBase P E + (model.updateCount : ℤ) * X)
    ((model.updateCount : ℤ) * X)

/-- At `updateCount = 0` the raise `X` does not matter. -/
theorem SolverTreeBudgetInv.of_updateCount_zero {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {G : MGraph} {P E : ℕ}
    {X X' : ℤ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (h0 : model.updateCount = 0) (h : SolverTreeBudgetInv G P E X model tok mem) :
    SolverTreeBudgetInv G P E X' model tok mem := by
  obtain ⟨hc, hr, ha, hs, hn⟩ := h
  refine ⟨hc, hr, ha, hs, ?_⟩
  rw [h0] at hn ⊢
  simpa using hn

/-- `SolverTreeBudgetInv` reads memory only at the record pointers of the live edges. -/
theorem SolverTreeBudgetInv.of_agree {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {G : MGraph} {P E : ℕ}
    {X : ℤ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    (h : SolverTreeBudgetInv G P E X model tok mem)
    (hag : ∀ e ∈ model.extG.E, mem' (tok.edgeRecords + model.extToInt e) =
      mem (tok.edgeRecords + model.extToInt e)) :
    SolverTreeBudgetInv G P E X model tok mem' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.of_agree hag, h.2.2.2.2⟩

/-! ## 3. The records at the start of `Update` -/

/-- The threshold of a length in `[2^{-E}, ∞)` lies in `[0, 2^(P + 2E + 1)]`. -/
theorem detectorThreshold_range_of_len {P E : ℕ} {ε len : ℝ} (hε : 0 < ε)
    (hεE : ε ≤ (2 : ℝ) ^ E) (hlen : (2 : ℝ) ^ (-(E : ℤ)) ≤ len) :
    0 ≤ detectorThreshold P ε len ∧ detectorThreshold P ε len ≤ (2 : ℤ) ^ (P + 2 * E + 1) := by
  have hl : 1 / (2 : ℝ) ^ E ≤ len := by rwa [zpow_neg, zpow_natCast, ← one_div] at hlen
  have hlenPos : 0 < len := lt_of_lt_of_le (by positivity) hl
  refine ⟨(detectorThreshold_pos P ε len hε hlenPos).le, ?_⟩
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hsc := detectorThreshold_scaled_bound P E ε len hεE hl
  rw [div_le_iff₀ hp, ← pow_add] at hsc
  have : ((detectorThreshold P ε len : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (P + 2 * E + 1) : ℤ) : ℝ) := by
    push_cast; rw [show P + 2 * E + 1 = 2 * E + 1 + P by omega]; exact hsc
  exact_mod_cast this

/-- The threshold of a length in range is at most `B₀`. -/
theorem abs_detectorThreshold_le_base {P E : ℕ} {ε len : ℝ} (hε : 0 < ε)
    (hεE : ε ≤ (2 : ℝ) ^ E) (hlen : (2 : ℝ) ^ (-(E : ℤ)) ≤ len) :
    |detectorThreshold P ε len| ≤ treeBudgetBase P E := by
  obtain ⟨h0, h1⟩ := detectorThreshold_range_of_len (P := P) hε hεE hlen
  rw [abs_of_nonneg h0]
  exact h1.trans (pow_le_pow_right₀ (by norm_num) (by omega))

/-- An integer whose value at precision `P` is at most `2^E` in size is at most `B₀` in size. -/
theorem abs_int_le_base_of_scaled {z : ℤ} {x : ℝ} {P E : ℕ}
    (hz : (z : ℝ) / (2 : ℝ) ^ P = x) (hx : |x| ≤ (2 : ℝ) ^ E) :
    |z| ≤ treeBudgetBase P E := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hzx : (z : ℝ) = x * (2 : ℝ) ^ P := by rw [← hz]; field_simp
  have h1 : |(z : ℝ)| ≤ (2 : ℝ) ^ (P + 2 * E + 2) := by
    rw [hzx, abs_mul, abs_of_pos hp]
    calc |x| * (2 : ℝ) ^ P ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ P := by gcongr
      _ = (2 : ℝ) ^ (E + P) := by rw [pow_add]
      _ ≤ (2 : ℝ) ^ (P + 2 * E + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : ((|z| : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (P + 2 * E + 2) : ℤ) : ℝ) := by
    push_cast; exact h1
  exact_mod_cast h2

/-- A detector `account − thr` with `0 ≤ account / 2^P`, `len · (account / 2^P) < ε` and
`thr ∈ [0, 2^(P + 2E + 1)]` is at most `B₀` in size. -/
theorem abs_detector_le_base {account thr : ℤ} {acc len ε : ℝ} {P E : ℕ}
    (hacc : (account : ℝ) / (2 : ℝ) ^ P = acc) (hacc0 : 0 ≤ acc) (hlt : len * acc < ε)
    (hlen : (2 : ℝ) ^ (-(E : ℤ)) ≤ len) (hεE : ε ≤ (2 : ℝ) ^ E)
    (hthr0 : 0 ≤ thr) (hthr : thr ≤ (2 : ℤ) ^ (P + 2 * E + 1)) :
    |account - thr| ≤ treeBudgetBase P E := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hE : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  have hl : 1 / (2 : ℝ) ^ E ≤ len := by rwa [zpow_neg, zpow_natCast, ← one_div] at hlen
  have hacc2 : acc ≤ (2 : ℝ) ^ (2 * E) := by
    have h1 : acc * (1 / (2 : ℝ) ^ E) ≤ acc * len := mul_le_mul_of_nonneg_left hl hacc0
    have h2 : acc * len < (2 : ℝ) ^ E := by rw [mul_comm]; exact lt_of_lt_of_le hlt hεE
    have h3 : acc * (1 / (2 : ℝ) ^ E) < (2 : ℝ) ^ E := lt_of_le_of_lt h1 h2
    rw [mul_one_div, div_lt_iff₀ hE, ← pow_add] at h3
    rw [show 2 * E = E + E by ring]; exact h3.le
  have haccZ : (account : ℝ) = acc * (2 : ℝ) ^ P := by rw [← hacc]; field_simp
  have hA0 : (0 : ℝ) ≤ account := by rw [haccZ]; positivity
  have hA1 : (account : ℝ) ≤ (2 : ℝ) ^ (P + 2 * E) := by
    rw [haccZ, pow_add, mul_comm ((2 : ℝ) ^ P)]
    exact mul_le_mul_of_nonneg_right hacc2 hp.le
  have hA0' : 0 ≤ account := by exact_mod_cast hA0
  have hA1' : account ≤ (2 : ℤ) ^ (P + 2 * E) := by exact_mod_cast hA1
  have hpow1 : (2 : ℤ) ^ (P + 2 * E) ≤ (2 : ℤ) ^ (P + 2 * E + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow2 : (2 : ℤ) ^ (P + 2 * E + 1) ≤ (2 : ℤ) ^ (P + 2 * E + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  unfold treeBudgetBase
  rw [abs_le]; constructor <;> linarith

/-- **The records at the start of `Update`.** Given the rep, each off-tree record has
`forward = true`, gradient `extg e · 2^P`, length `extℓ e · 2^P`, flow `flow e · 2^P` and detector
`detectAccum e · 2^P − thr` (`SolverEdgeOrientInv`, `SolverEdgeAccountsAt`; a block decodes to
one value, `pathEdgeAt_unique`). So the model bounds give `OffTreeRecInv` and `OffTreeRecBound`
at every `B ≥ B₀`, with the separation of the blocks given. -/
theorem offTreeRec_of_model {cfg : Alg2Config} {L P m V psi k epsExp drainUnit E : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ} {B : ℤ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hε : 0 < cfg.ε) (hεE : cfg.ε ≤ (2 : ℝ) ^ E) (hB : treeBudgetBase P E ≤ B)
    (hrange : ∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ E ∧
      (2 : ℝ) ^ (-(E : ℤ)) ≤ model.extℓ e ∧ model.extℓ e ≤ (2 : ℝ) ^ E)
    (hflow : ∀ e ∈ model.extG.E, |model.flow e| ≤ (2 : ℝ) ^ E)
    (hacc : ∀ e ∈ model.extG.E, 0 ≤ model.detectAccum e ∧
      model.extℓ e * model.detectAccum e < cfg.ε)
    (hsep : OffTreeRecSep model L mem tok.edgeRecords) :
    OffTreeRecInv model L mem tok.edgeRecords B ∧ OffTreeRecBound model L mem tok.edgeRecords B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hedgeAcc, _, _, _, _, hwire, _⟩ := hrep
  have horient := hwire.2.2.2.2
  have hval (e : ℕ) (he : e ∈ model.extG.E)
      (hnot : model.extToInt e ∉ model.chain.toTreeChain.chainTree.E) (val : PathEdgeValue)
      (hpa : PathEdgeAt mem (mem (tok.edgeRecords + model.extToInt e)) 4 L (some val)) :
      |val.detector| ≤ B ∧ |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B := by
    have ho := horient e he
    dsimp only at ho
    rw [if_neg hnot] at ho
    obtain ⟨hfwd, hgr, hln⟩ := ho val hpa
    have hea := hedgeAcc.1 e he
    dsimp only at hea
    obtain ⟨_, _, hrec⟩ := hea
    rw [if_neg hnot] at hrec
    obtain ⟨_, val₀, account, hpa₀, hfl, hac, hdet, _⟩ := hrec
    have hv : val = val₀ := Option.some.inj (LinkCut.Path.pathEdgeAt_unique hpa hpa₀)
    subst hv
    have hgr' : (val.gradient : ℝ) / (2 : ℝ) ^ P = model.extg e := by
      simpa [PathEdgeValue.originalGradient, hfwd] using hgr
    have hfl' : (val.flow : ℝ) / (2 : ℝ) ^ P = model.flow e := by
      simpa [PathEdgeValue.originalFlow, hfwd] using hfl
    obtain ⟨hg, hl0, hl1⟩ := hrange e he
    have hlpos : 0 < model.extℓ e := lt_of_lt_of_le (by positivity) hl0
    have hlabs : |model.extℓ e| ≤ (2 : ℝ) ^ E := by rw [abs_of_pos hlpos]; exact hl1
    obtain ⟨ht0, ht1⟩ := detectorThreshold_range_of_len (P := P) hε hεE hl0
    refine ⟨?_, (abs_int_le_base_of_scaled hgr' hg).trans hB,
      (abs_int_le_base_of_scaled hln hlabs).trans hB,
      (abs_int_le_base_of_scaled hfl' (hflow e he)).trans hB⟩
    rw [hdet]
    exact (abs_detector_le_base hac (hacc e he).1 (hacc e he).2 hl0 hεE ht0 ht1).trans hB
  exact ⟨⟨fun e he hnot val hpa => (hval e he hnot val hpa).1, hsep⟩,
    fun e he hnot val hpa => (hval e he hnot val hpa).2⟩

/-- After `Detect`, every live accumulator is below its threshold: a reported edge is reset to
`0`, and an edge that is not reported has `extℓ e · detectAccum e < ε`. -/
theorem algorithm2_detect_accum_lt {cfg : Alg2Config} (st : Alg2State cfg) (hε : 0 < cfg.ε)
    (ha : ∀ e, 0 ≤ st.detectAccum e) (e : ℕ) (he : e ∈ st.extG.E) :
    0 ≤ (algorithm2_detect cfg st).2.detectAccum e ∧
      (algorithm2_detect cfg st).2.extℓ e * (algorithm2_detect cfg st).2.detectAccum e < cfg.ε := by
  dsimp only [algorithm2_detect]
  split_ifs with hS
  · exact ⟨le_rfl, by simpa using hε⟩
  · refine ⟨ha e, ?_⟩
    have : ¬ cfg.ε ≤ st.extℓ e * st.detectAccum e := fun h =>
      hS (Finset.mem_filter.mpr ⟨he, h⟩)
    exact lt_of_not_ge this

/-! ## 4. The fit -/

/-- **The fit of the budget.** With `c ≤ 2 G.m + 1` updates, `B₀ + 2 G.m X ≤ B_bound`,
`2 G.m X ≤ R_bound` and the fit at `B_bound + X`, `R_bound + X`, the budget `B₀ + c X`, `c X`
fits: `c X ≤ 2 G.m X + X`. -/
theorem treeBudget_fit {c Gm n : ℕ} {B₀ X B_bound R_bound cap : ℤ} (hX : 0 ≤ X)
    (hc : c ≤ 2 * Gm + 1) (hB : B₀ + 2 * (Gm : ℤ) * X ≤ B_bound) (hR : 2 * (Gm : ℤ) * X ≤ R_bound)
    (hcap : 2 * ((2 * n + 1 : ℕ) : ℤ) * ((B_bound + X) + (R_bound + X)) < cap) :
    2 * ((2 * n + 1 : ℕ) : ℤ) * ((B₀ + (c : ℤ) * X) + (c : ℤ) * X) < cap := by
  have hcZ : (c : ℤ) ≤ 2 * (Gm : ℤ) + 1 := by exact_mod_cast hc
  have hcX : (c : ℤ) * X ≤ 2 * (Gm : ℤ) * X + X := by nlinarith
  have hsum : (B₀ + (c : ℤ) * X) + (c : ℤ) * X ≤ (B_bound + X) + (R_bound + X) := by linarith
  have hk : (0 : ℤ) ≤ 2 * ((2 * n + 1 : ℕ) : ℤ) := by positivity
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsum hk) hcap

end MinCostFlow.MinRatio
